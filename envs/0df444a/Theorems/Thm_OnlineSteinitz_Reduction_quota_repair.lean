-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_quota_repair
-- name    : OnlineSteinitz.Reduction.quota_repair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:38.898135+00:00
-- url     : https://prove2.me/theorems/79ec5a6f-3c07-45a6-8e51-2ae8809d31de
-- title:
--   Lemma 2.3 — one-node quota repair and conditional MGFs
-- statement:
--   Let an internal node of capacity $m\ge2$ receive Euclidean unit-ball vectors $x_1,\ldots,x_m$. For arbitrary proposed signs $\varepsilon_i$, perform Algorithm 1 quota repair, with $+1$ denoting left. Set $\mu=m^{-1}\sum_i x_i$, $q=\sum_i\varepsilon_i$ and $Y=\sum_i\varepsilon_i(x_i-\mu)$. The actual proportional split error satisfies
--   $$\operatorname{err}=\tfrac12Y+R,\qquad\|R\|_2\le|q|+1.$$
--   Under the terminal scale hypothesis (2.2), with $\Sigma\ge1$, fix an oblivious global unit-ball stream. At every internal node $u$, for every Euclidean unit vector $z$ and every real $\lambda$, the two exponentials are integrable and, almost surely conditional on its strict ancestors' complete tapes,
--   $$\mathbb E[e^{\lambda\langle z,Y_u\rangle/2}\mid\operatorname{anc}(u)]\le e^{\Sigma^2\lambda^2/2},\qquad
--   \mathbb E[e^{\lambda q_u}\mid\operatorname{anc}(u)]\le e^{\Sigma^2\lambda^2}.$$
--   The statement preserves both the deterministic repair assertion and the two conditional moment estimates. The streams at individual nodes may be random through ancestor routing; node errors are not assumed independent.
--
--   Differences from the source:
--   - encoding: positions and arrivals indexed from 1 → zero-based slots and arrivals, with half-open intervals [a,a+m); reason: subtracting one from indices preserves every input and prefix, including k=0,T; values outside the first T slots are ignored
--   - encoding: persistent signer state updated with proposed signs and supplied routing statistics → a tape-dependent function of the current vector and the local vector/proposed-sign history; reason: the capacity is known and quota repair reconstructs all child counts, sums and remaining capacities from this history; state can be replayed without consulting future vectors or descendant tapes
--   - encoding: independent private tapes at the internal nodes → a finite product probability law on an interval grid, with arbitrary measurable tape carrier and node-specific marginal laws; reason: unused coordinates are dummy independent tapes; the router reads only visited nodes, while ancestor conditioning retains the complete tapes
--   - encoding: ordinary and conditional expectations of exponentials → Bochner integrals and almost-everywhere conditional expectations, with integrability asserted in Lemma 2.3; reason: fixed-input execution has finitely many measurable sign outcomes, so these exponentials are integrable; no integrability premise or finite input alphabet is added
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, Lemma 2.3, p.8, equations (2.7)–(2.8); R defined on p.9

import Definitions.Def_OnlineSteinitz_Reduction_Randomness

open MeasureTheory

namespace OnlineSteinitz.Reduction

/-- Full Lemma 2.3, p.8: local decomposition, remainder bound and both
conditional MGFs. Integrability is asserted, never assumed. -/
theorem quota_repair :
    (∀ (d m : ℕ), 0 < d → 2 ≤ m →
      ∀ (x : Fin m → Vec d) (ε : Fin m → Bool), (∀ i, ‖x i‖ ≤ 1) →
        let h := repair m (List.ofFn (fun i => (x i, ε i)))
        localError m h = (1 / 2 : ℝ) • centeredSum h + remainder m h ∧
          ‖remainder m h‖ ≤ |signedCount (proposedHistory h)| + 1) ∧
    (∀ (T d : ℕ), 0 < T → 0 < d →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Node T → Measure Ω)
        [∀ u, IsProbabilityMeasure (μ u)]
        (r : Node T → Signer (Vec (d + 1)) Ω),
      (∀ u ∈ internalNodes T, MeasurableSigner (r u)) →
      ∀ sigma : ℝ, 1 ≤ sigma →
      (∀ u ∈ internalNodes T, HasScale (μ u) u.2.val (r u) sigma) →
      ∀ v : Fin T → Vec d, (∀ i, ‖v i‖ ≤ 1) →
      ∀ u ∈ internalNodes T, ∀ z : Vec d, ‖z‖ = 1 → ∀ lam : ℝ,
        Integrable (directionExp r v u z lam) (tapeLaw μ) ∧
        Integrable (countExp r v u lam) (tapeLaw μ) ∧
        (∀ᵐ ω ∂tapeLaw μ,
          (tapeLaw μ)[directionExp r v u z lam | ancestorSigma u] ω ≤
            Real.exp (sigma ^ 2 * lam ^ 2 / 2)) ∧
        (∀ᵐ ω ∂tapeLaw μ,
          (tapeLaw μ)[countExp r v u lam | ancestorSigma u] ω ≤
            Real.exp (sigma ^ 2 * lam ^ 2))) := by sorry

end OnlineSteinitz.Reduction
