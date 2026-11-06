-- Prove2me | Theorems.Thm_GradedReserve_theorem_3_1
-- name    : GradedReserve.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:30.649346+00:00
-- url     : https://prove2.me/theorems/2d553649-ecdf-4042-80cc-63da6b828347
-- title:
--   Theorem 3.1 — for $F(v)=v^k$ the graded reserve $\min\{(b/b_0)^p,1\}$ is optimal
-- statement:
--   Let $F(v)=v^k$ with real $k\ge1$ and $n\ge2$, and write $m=k(n-1)$, $\ell=m+1$, $N=kn$. For $p>p_{\min}=\frac12\big(\sqrt{\ell^2+4km}-\ell\big)$ let
--   $$\bar v^{\,k}=\frac1{k+1}\Big(1-\frac{km}{p(p+\ell)}\Big),\qquad b_0=\bar v\,\frac{p+m}{p+\ell}.$$
--   Fix $\varepsilon\in(0,1)$, put $\tau=(1-\varepsilon)R^*$, and assume $R_n(0)<\tau$ (the standing assumption of Section 3). The equation
--   $$R_n(0)+\frac n\ell\,\bar v^{\,\ell}\,\frac p{p+\ell}-\frac{n(k+1)}{N+1}\,\bar v^{\,N+1}\,\frac p{p+N+1}=\tau\qquad(3)$$
--   has a unique root $p>p_{\min}$, and for this $p$:
--
--   1. $G_{\pi^*}$ with $\pi^*(b)=\min\{(b/b_0)^p,1\}$ is $\tau$-admissible, and every $\tau$-admissible $G_\pi\in G$ satisfies
--   $$\mathrm{Rev}_{\mathrm{anc}}(G_\pi)\le\mathrm{Rev}_{\mathrm{anc}}(G_{\pi^*})=\frac N{N+1}\Big[1-b_0^{N+1}\frac p{p+N+1}\Big].$$
--   2. In equilibrium the probability of sale is $s^*(v)=\min\{(v/\bar v)^p,1\}$: every positive bid wins with positive probability and sale is certain from $\bar v<1$ on. The equilibrium bid is $\frac{p+m}{p+\ell}v$ for $v\le\bar v$ and $\frac m\ell v+\frac{p\bar v^{\,\ell}}{\ell(p+\ell)v^m}$ for $v\ge\bar v$.
--
--   The theorem gives the revenue-maximizing graded reserve for anchored bidders, among all graded reserves whose every symmetric equilibrium guarantees a $(1-\varepsilon)$ share of the optimal revenue from rational bidders, in closed form up to the scalar $p$.
--
--   **Formalization Note** Part 2 is stated as: $\beta^*$ is a symmetric equilibrium of $G_{\pi^*}$ with $\pi^*(\beta^*(v))=s^*(v)$, and every symmetric equilibrium of $G_{\pi^*}$ plays $\beta^*(v)$ for almost every type.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: a distribution F on [0,1] whose density f is positive on (0,1) → IsValueDensity f (f measurable, ≥ 0 on [0,1], > 0 on (0,1), ∫₀¹ f = 1), F(v) = ∫₀^v f; reason: the paper's model; the same distributions
--   - encoding: symmetric BNE β, mixed strategies allowed (p.13), with an exit action → a Markov kernel σ from values to actions in ℝ; negative actions are exit, bids lie in [0,1], no mass above 1; reason: Lean convention (no measurable space on Option ℝ); the same strategies
--   - reading: a Bayes–Nash equilibrium (every type best-responds) → almost every type (for the value law) best-responds; reason: the paper's proofs work up to null sets of types ("apart from a null set", p.14); a single type has probability zero
--   - encoding: sells to the highest bidder with probability π(b₍₁₎); ties broken uniformly at random → W(b) = π(b) Σ_j C(n−1,j) a^j c^{n−1−j}/(j+1) against n − 1 i.i.d. opponents; reason: the same winning probability
--   - encoding: non-decreasing π : [0,1] → [0,1] → π : ℝ → ℝ, monotone with values in [0,1] on [0,1]; reason: only values on [0,1] are used; the same mechanisms
--   - encoding: Rev_anc(G_π) = E[V₍₁₎ π(V₍₁₎)], the revenue when all bidders are anchored → revRat of the truthful profile σ(v) = δ_v; reason: the revenue of anchored bidders; the same number
--   - encoding: R_n(r) = n ∫_r^1 φ Q f → n ∫_r^1 (v f(v) − (1 − F(v))) Q(v) dv; reason: equal wherever f > 0, i.e. almost everywhere; avoids x/0 = 0
--   - encoding: Section 3: R_n(0) < τ < R* → hypothesis R_n(0) < (1 − ε)R*; reason: τ = (1 − ε)R* < R* because ε > 0 and R* > 0 for the power law; nothing is excluded
--   - encoding: for this p (the unique root) → for every p > p_min with lhs3 p = τ; reason: equivalent given the first clause; avoids a choice function
--   - reading: In equilibrium the probability of sale is s*(v) … The equilibrium bid is β* → β* is a symmetric BNE of G_{π*} with π*(β*(v)) = s*(v), and every symmetric BNE σ of G_{π*} has σ(v) = δ_{β*(v)} for a.e. v; reason: "the equilibrium" refers to every symmetric BNE, which Lemma 3.3 licenses because every v > 0 trades; the stronger reading
--   - reading: every positive bid wins with positive probability → π*(b) > 0 for every b ∈ (0,1]; reason: in the equilibrium β* every bid b > 0 is above the bids of opponents with types near 0, so b wins with positive probability exactly when π*(b) > 0
--   - encoding: the equilibrium bid β* (a pure strategy) → the deterministic kernel v ↦ δ_{β*(v)}, with measurability of β* part of the conclusion; reason: the same strategy
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6); proof pp.18–20 (PDF 19–21)

import Mathlib
import Definitions.Def_GradedReserve_IsGradedReserve
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_IsTauAdmissible
import Definitions.Def_GradedReserve_bZero
import Definitions.Def_GradedReserve_betaStar
import Definitions.Def_GradedReserve_lhs3
import Definitions.Def_GradedReserve_optRevenue
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_piStar
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_revAnc
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_sStar
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_vbar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Theorem 3.1** (Optimal graded reserve) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6; proof pp.18–20, PDF
19–21). Let `F(v) = v^k` with `k ≥ 1` and `n ≥ 2`, `m = k(n − 1)`, `ℓ = m + 1`, `N = kn`, fix
`ε ∈ (0, 1)`, `τ = (1 − ε) R*`, and assume Section 3's `R_n(0) < τ`. Equation (3) has a unique root
`p > p_min`, and for this `p`:
1. `G_{π*}` with `π*(b) = min{(b/b₀)^p, 1}` is `τ`-admissible, and every `τ`-admissible
   `G_π ∈ G` satisfies `Rev_anc(G_π) ≤ Rev_anc(G_{π*}) = (N/(N+1))[1 − b₀^{N+1} p/(p+N+1)]`.
2. In equilibrium the probability of sale is `s*(v) = min{(v/v̄)^p, 1}`: every positive bid wins
   with positive probability and sale is certain from `v̄ < 1` on. The equilibrium bid is `β*`
   of (30).

**Formalization Note.** "For this `p`" is stated for every `p > p_min` solving (3), which by the
first clause is the unique root. Part 2 is read for every symmetric BNE: `β*` is a symmetric BNE
with `π*(β*(v)) = s*(v)`, and every symmetric BNE of `G_{π*}` plays `β*(v)` for almost every type.
`τ < R*` holds automatically (`ε > 0`, `R* > 0`). -/
theorem theorem_3_1 (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1)
    (hτ : revCurve (powerDensity k) n 0 < (1 - ε) * optRevenue (powerDensity k) n) :
    (∃! p, pMin k n < p ∧ lhs3 k n p = (1 - ε) * optRevenue (powerDensity k) n) ∧
    ∀ p, pMin k n < p → lhs3 k n p = (1 - ε) * optRevenue (powerDensity k) n →
      IsTauAdmissible (powerDensity k) n ((1 - ε) * optRevenue (powerDensity k) n)
        (piStar k n p) ∧
      (∀ π : ℝ → ℝ, IsGradedReserve π →
        IsTauAdmissible (powerDensity k) n ((1 - ε) * optRevenue (powerDensity k) n) π →
        revAnc (powerDensity k) n π ≤ revAnc (powerDensity k) n (piStar k n p)) ∧
      revAnc (powerDensity k) n (piStar k n p) =
        powN k n / (powN k n + 1)
          * (1 - bZero k n p ^ (powN k n + 1) * (p / (p + powN k n + 1))) ∧
      (∃ hβ : Measurable (betaStar k n p),
        IsSymBNE (powerDensity k) n (piStar k n p) (Kernel.deterministic (betaStar k n p) hβ)) ∧
      (∀ v ∈ Icc (0:ℝ) 1, piStar k n p (betaStar k n p v) = sStar k n p v) ∧
      (∀ σ : Kernel ℝ ℝ, IsSymBNE (powerDensity k) n (piStar k n p) σ →
        ∀ᵐ v ∂(typeMeasure (powerDensity k)), σ v = Measure.dirac (betaStar k n p v)) ∧
      (∀ b ∈ Ioc (0:ℝ) 1, 0 < piStar k n p b) ∧
      vbar k n p < 1 ∧ (∀ v ∈ Icc (vbar k n p) 1, sStar k n p v = 1) := by sorry

end GradedReserve
