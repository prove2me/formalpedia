-- Prove2me | Theorems.Thm_GnpColoring_theorem_5_3
-- name    : GnpColoring.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:14.298234+00:00
-- url     : https://prove2.me/theorems/c92936ef-9315-4e6b-ad29-43d6c83a021e
-- title:
--   Theorem 5.3 — uniform within-block relaxation
-- statement:
--   There are absolute constants $c_0,c_1>0$ such that, for $A\ge1$, $C>0$, $0<\eta<\varepsilon\le1/2$ and all sufficiently large $d$, and every fixed $D>0$, with probability $1-o(1)$ over $G\sim G(n,d/n)$ the following holds for every integer $q\ge d+d^{1/2+\varepsilon}$. For every tree or unicyclic block $B$ whose exterior boundary consists of global breakpoints and every feasible exterior colouring $\tau$, with $b_B=\operatorname{diam}(G[B])$,
--
--   $$\tau_{\mathrm{rel}}(B,\tau)\le\exp\Big\{c_0\Big[\Big(b_B+1+\frac{\log n}{d^{2\eta}}\Big)\log q+\frac{\log n}{q}\Big]\Big\},\tag{5.1}$$
--
--   and, if $b_B\le D\log n/d^{2\eta}$, then $\tau_{\mathrm{rel}}(B,\tau)\le n^{\zeta_d}$ with $\zeta_d=c_1(D+1)\log q/d^{2\eta}$, so $T_*\le n^{\zeta_d}$ (5.2).
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - encoding: "tree or unicyclic block whose exterior boundary consists of global breakpoints" → any vertex set $B$ with $G[B]$ a connected tree or unicyclic graph and $\partial B\subseteq\hat S$; reason: such a $B$ is a component of $G$ after deleting $\partial B\subseteq\hat S$, i.e. a block
--   - encoding: $T_*:=\max\{1,\sup_{B,\tau}\tau_{\mathrm{rel}}\}\le n^{\zeta_d}$ → `RelaxBound` with constant $n^{\zeta_d}$ for each $B,\tau$; reason: $n^{\zeta_d}\ge1$; the sup bound is the bound for each $B,\tau$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Theorem 5.3, Eqs. (5.1)–(5.2), p.44

import Mathlib
import Definitions.Def_GnpColoring_IsTreeOrUnicyclic
import Definitions.Def_GnpColoring_extBoundary
import Definitions.Def_GnpColoring_globalBreakpoints
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_RelaxBound
import Definitions.Def_GnpColoring_blockDiam
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Theorem 5.3 (uniform within-block relaxation).** There are absolute constants `c₀, c₁ > 0` such
that, in the regime of Section 5.1 (`A ≥ 1`, `C > 0`, `0 < η < ε ≤ 1/2`, `d` large), with probability
`1 − o(1)` over `G ∼ G(n, d/n)`: for every integer `q ≥ d + d^(1/2+ε)`, every tree or unicyclic block
`B` whose exterior boundary consists of global breakpoints and every feasible exterior colouring `τ`,
with `b_B = diam(G[B])`,
(5.1) `τ_rel(B, τ) ≤ exp{c₀[(b_B + 1 + log n/d^(2η)) log q + log n/q]}`, and
(5.2) for any fixed `D > 0`, if `b_B ≤ D log n/d^(2η)` then `τ_rel(B, τ) ≤ n^(ζ_d)`,
`ζ_d = c₁(D + 1) log q / d^(2η)` (so `T∗ ≤ n^(ζ_d)`).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Theorem 5.3, p.44: "Here d is fixed before taking n → ∞, and the event and the lower
threshold on n can be chosen independently of q."

**Formalization Note** `q` is quantified inside the event (as the theorem states). A "block" is
any vertex set `B` with `G[B]` a connected tree or unicyclic graph and `∂B ⊆ Ŝ`; such a `B` is a
connected component of `G` after removing `∂B ⊆ Ŝ`, so this is the paper's notion. `τ_rel ≤ X` is
`RelaxBound … X` (both bounds are `≥ 1`). `D` is fixed before `n → ∞` ("for any fixed diameter
constant D and all sufficiently large n"). -/
theorem theorem_5_3 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ A : ℝ, 1 ≤ A → ∀ C : ℝ, 0 < C → ∀ η ε : ℝ, 0 < η → η < ε → ε ≤ 1 / 2 →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d → ∀ D : ℝ, 0 < D →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          ∀ q : ℕ, d + d ^ ((1 : ℝ) / 2 + ε) ≤ (q : ℝ) →
            ∀ B : Finset (Fin n), IsTreeOrUnicyclic G B →
              extBoundary G B ⊆ globalBreakpoints G d η A C →
              ∀ x : Fin n → Fin q, IsFeasible G q B x →
                RelaxBound G q B x (Real.exp (c₀ * (((blockDiam G B : ℝ) + 1 +
                    Real.log n / d ^ (2 * η)) * Real.log q + Real.log n / q))) ∧
                ((blockDiam G B : ℝ) ≤ D * Real.log n / d ^ (2 * η) →
                  RelaxBound G q B x ((n : ℝ) ^ (c₁ * (D + 1) * Real.log q / d ^ (2 * η))))))
        atTop (𝓝 1) := by sorry

end GnpColoring
