-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_3
-- name    : GevreyGibbsSep.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:45:01.025106+00:00
-- url     : https://prove2.me/theorems/a61543a5-207a-44ec-aae9-1d434eeb1d17
-- title:
--   Theorem 3 — hide-and-seek lower bound $N_{\mathrm{cl}}\ge(2\pi)^d(\delta-\varepsilon)/v_0-1$
-- statement:
--   Let $p_0$ be a bump (Definition B.4) on a closed patch $\Omega_0\subset\mathbb T^d$ of volume $v_0\in(0,(2\pi)^d)$ with concentration $\delta$, given as the Gibbs state of a periodic potential $V_0$. Let $\mathcal P$ be any instance class containing all shifts $p_g(A)=p_0(A-g)$, $g\in\mathbb T^d$ (potentials $V_0(\cdot-g)$). Then for every oracle order $k\in\mathbb N\cup\{\infty\}$ and every accuracy $\varepsilon<\delta$,
--   $$N_{\mathrm{cl}}(\mathcal P,\varepsilon)\ \ge\ (2\pi)^d\,\frac{\delta-\varepsilon}{v_0}-1 .$$
--
--   With $M=(2\pi)^d/v_0$ hiding places the bound reads $N_{\mathrm{cl}}\ge M(\delta-\varepsilon)-1$: sampling accurately means finding a randomly placed patch, and each query inspects one of about $M$ places.
--
--   Differences from the source:
--   - generalization: $\mathcal P$ is a class accessed by the oracle (densities with $C^k$ lifts) → $V_0$ is only assumed $2\pi$-periodic and $\mathcal P$ is any set of potentials containing the shifts; reason: the argument is regularity-agnostic (p.14); the oracle is defined for every potential
--   - generalization: accuracy $\varepsilon$ with $0<\varepsilon<\delta$ (Definition 3 takes $\varepsilon>0$) → every real $\varepsilon<\delta$; reason: for $\varepsilon\le0$ no algorithm is accurate, $N_{\mathrm{cl}}=\infty$, and the statement is true; it specializes to the source's range
--   - encoding: shifts $g\in\mathbb T^d$ → shifts by $g\in\mathbb R^d$ (lifts of torus points); reason: every torus shift has a lift and every real shift is a torus shift
--   - generalization: output maps $\Psi_n$, $n\ge1$ → an output $\widehat X_0$ with no query is also allowed; reason: a larger class of algorithms can only lower $N_{\mathrm{cl}}$, so the lower bound is at least as strong
--   - reading: a seed $\omega\sim P$ and maps $Q_n,\Psi_n$, with the output law the distribution over the seed → an arbitrary probability space of seeds and jointly measurable $Q_n,\Psi_n$; reason: the output law is only defined for measurable maps; the seed space is not restricted to countable ones
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $N_{\mathrm{cl}}\ge B$ in $\mathbb N\cup\{\infty\}$ → $\max(B,0)\le N_{\mathrm{cl}}$ in $[0,\infty]$; reason: the same inequality; a negative bound is trivially true in both
--   - encoding: the order-$k$ answer $\phi_k(p,x)=(\nabla^{\otimes j}\log\bar p(x))_{j=0}^{k}$ at a representative of $x$, $k\in\mathbb N\cup\{\infty\}$ → the family of all iterated partials $\partial_{i_1}\cdots\partial_{i_j}\log\bar p$ of every order $j$ at the $[0,2\pi)^d$ representative of $x$, with the entries of order $j>k$ set to $0$, and $k\in\mathbb N\cup\{\top\}$; reason: the entries of order $j\le k$ are the components of $\nabla^{\otimes j}\log\bar p(x)$ and the padded zeros carry no information, so every algorithm sees the same answers
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem 3, Eq. (27), p.12; proof in Appendix B 2, pp.36–37

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_Ncl
import Definitions.Def_GevreyGibbsSep_IsBump

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem 3 (hide-and-seek lower bound on `T^d`), arXiv:2608.24527 (sha256 d4fd40eb…),
Eq. (27), p.12. Let the Gibbs state of `V₀` be a bump on a closed patch `Ω₀` of volume
`v₀ ∈ (0, (2π)^d)` with concentration `δ`, and let `P` contain every shift
`V₀(· − g)`, `g ∈ ℝ^d`. Then for every oracle order `k ∈ ℕ ∪ {∞}` and every `ε < δ`,
`N_cl(P, ε) ≥ (2π)^d (δ − ε)/v₀ − 1`.

**Formalization Note** No regularity of `V₀` beyond periodicity is assumed (the bound is
regularity-agnostic, as the paper notes on p.14); the comparison is in `ℝ≥0∞`. -/
theorem theorem_3 {d : ℕ} (V₀ : (Fin d → ℝ) → ℝ)
    (hper : ∀ (x : Fin d → ℝ) (i : Fin d), V₀ (x + Pi.single i (2 * Real.pi)) = V₀ x)
    (Ω₀ : Set (Torus d)) (δ κ : ℝ) (hbump : IsBump V₀ Ω₀ δ κ)
    (P : Set ((Fin d → ℝ) → ℝ)) (hP : ∀ g : Fin d → ℝ, (fun x => V₀ (x - g)) ∈ P)
    (k : ℕ∞) (ε : ℝ) (hε : ε < δ) :
    ENNReal.ofReal ((2 * Real.pi) ^ d * (δ - ε) / (volume Ω₀).toReal - 1)
      ≤ (Ncl d k P ε : ℝ≥0∞) := by sorry

end GevreyGibbsSep
