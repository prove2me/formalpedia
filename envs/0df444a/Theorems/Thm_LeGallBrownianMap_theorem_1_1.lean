-- Prove2me | Theorems.Thm_LeGallBrownianMap_theorem_1_1
-- name    : LeGallBrownianMap.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:58.584992+00:00
-- url     : https://prove2.me/theorems/8b4de6a6-2da7-4e3d-b7dc-bb805169af59
-- title:
--   Theorem 1.1 — uniform $q$-angulations with $n$ faces, rescaled by $c_q n^{-1/4}$, converge to the Brownian map
-- statement:
--   Let $q\ge3$ with $q=3$ or $q$ even. Let $M_n$ be uniformly distributed over the set $A^q_n$ of rooted planar $q$-angulations with $n$ faces (loops and multiple edges allowed; $n$ even if $q=3$), and let $m_n$ be its vertex set with the graph distance $d_{gr}$. Set $c_q=\big(9/(q(q-2))\big)^{1/4}$ for $q$ even and $c_3=6^{1/4}$. Let $(m_\infty,D^*)$ be the Brownian map built from a normalized Brownian excursion $e$ and Brownian labels $Z$. Then $(m_\infty,D^*)$ is a random compact metric space, which does not depend on $q$, and
--
--   $$
--   (m_n,\ c_q\, n^{-1/4} d_{gr})\xrightarrow[n\to\infty]{(d)}(m_\infty, D^*)
--   $$
--
--   in distribution in the space $\mathbb K$ of isometry classes of compact metric spaces with the Gromov–Hausdorff distance: for every bounded continuous $f:\mathbb K\to\mathbb R$, $\mathbb E[f(m_n,c_qn^{-1/4}d_{gr})]\to\mathbb E[f(m_\infty,D^*)]$.
--
--   This is the main theorem of the paper: it identifies the scaling limit of uniform triangulations and of uniform $2p$-angulations as one universal random metric space, solving Schramm's problem for triangulations.
--
--   **Formalization Note** The excursion is realized as the 3-dimensional Bessel bridge `OAI.FKCRT.standardExcursion B` and the statement holds for every probability space carrying three independent Brownian motions and Brownian labels. The limit is computed pathwise by `brownianMap`; the first conjunct asserts that it is an a.e.-measurable random variable in $\mathbb K$ (Borel $\sigma$-algebra), so that its law is well defined.
--
--   Differences from the source:
--   - encoding: a normalized Brownian excursion e and labels Z with the conditional law of §2.4 → e = OAI.FKCRT.standardExcursion B (norm of a 3-dimensional Brownian bridge) for three independent Brownian motions B, and Z with IsBrownianLabels (conditional characteristic functions), on any probability space; reason: the Bessel bridge has the law of the normalized excursion and the characteristic-function identity is the conditional Gaussian law; quantifying over all realizations pins the law
--   - encoding: rooted planar maps up to orientation-preserving homeomorphism (loops, multiple edges allowed) → rotation systems OAI.FKCRT.RootedMap with root dart 0, up to root-preserving isomorphism; q-angulation = every face cycle has q darts; reason: the standard combinatorial encoding of rooted planar maps; same objects, same counting
--   - encoding: m∞ = T_e/≃ with the distance D∗ of eq. (1) → [0,1]/{D∗ = 0} with the distance induced by D∗ (D∗ unfolded on [0,1]); reason: D∗(a,b) = 0 iff D°(a,b) = 0 for all a, b ∈ T_e almost surely ([15], Thm 3.4, quoted p.15), so the two metric spaces coincide a.s.
--   - encoding: convergence in distribution in K; (m∞, D∗) a random compact metric space → expectations of every bounded continuous f : K → ℝ converge; K = GHSpace with its Borel σ-algebra; a.e.-measurability of ω ↦ brownianMap as a conjunct; reason: definition of convergence in distribution; the conjunct makes the law of the limit well defined
--   - encoding: n → ∞ (n even when q = 3) → the filter atTop ⊓ 𝓟 {n | 1 ≤ n ∧ (q = 3 → Even n)}; reason: A^3_n is empty for odd n and the paper restricts to n ≥ 1
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 1.1, pp.2–3; Brownian map pp.3–4 and §2.3–2.4, pp.12–15

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_ghMeasurableSpace
import Definitions.Def_LeGallBrownianMap_cq
import Definitions.Def_LeGallBrownianMap_uniformMapExpectation
import Definitions.Def_LeGallBrownianMap_IsBrownianLabels
import Definitions.Def_LeGallBrownianMap_brownianMap

open MeasureTheory ProbabilityTheory Filter GromovHausdorff OAI.FKCRT
open scoped Topology NNReal BoundedContinuousFunction

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2,
Theorem 1.1, pp.2–3: "Set c_q = (9/(q(q − 2)))^{1/4} if q is even, and c_3 = 6^{1/4}. There exists
a random compact metric space (m∞, D∗) called the Brownian map, which does not depend on q, such
that (m_n, c_q n^{−1/4} d_gr) −(d)→ (m∞, D∗), where the convergence holds in distribution in the
space K." Here q ≥ 3 with q = 3 or q even, `M_n` is uniform on the rooted planar q-angulations
with `n` faces (n even if q = 3), and `(m∞, D∗)` is the Brownian map of pp.3–4.

Let `B = (B_0, B_1, B_2)` be three independent real Brownian motions on a probability space,
`e = standardExcursion B` the normalized Brownian excursion, and `Z` Brownian labels given `e`.
Then `ω ↦ (m∞, D∗)(ω) = brownianMap e Z` is a random variable in K (a.e.-measurable), and for
every bounded continuous `f : K → ℝ`, `E[f(m_n, c_q n^{−1/4} d_gr)] → E[f(m∞, D∗)]` as `n → ∞`
through `n ≥ 1` (through even `n` if `q = 3`).

**Formalization Note.** The normalized excursion is the published
`OAI.FKCRT.standardExcursion` (3-dimensional Bessel bridge `|b_t|`, `b` a 3-dimensional Brownian
bridge, which has the law of the normalized Brownian excursion). Quantifying over every
probability space, every such `B` and every `Z` pins the limit law, so the limit is a fixed law on
K; it does not mention `q`, which is "does not depend on q". Convergence in distribution in K
is convergence of expectations of all bounded continuous `f`, with K the Gromov–Hausdorff space
and its Borel σ-algebra. The exponent `−1/4` is a real power (`Real.rpow`). -/
theorem theorem_1_1 (q : ℕ) (hq : q = 3 ∨ (Even q ∧ 4 ≤ q))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Fin 3 → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (Z : unitInterval → Ω → ℝ) (hZ : IsBrownianLabels (fun ω => standardExcursion B ω) Z P) :
    AEMeasurable (fun ω => brownianMap (standardExcursion B ω) (fun t => Z t ω)) P ∧
    ∀ f : GHSpace →ᵇ ℝ,
      Tendsto (fun n : ℕ => uniformMapExpectation q n (cq q * (n : ℝ) ^ (-(1 / 4 : ℝ))) f)
        (atTop ⊓ 𝓟 {n : ℕ | 1 ≤ n ∧ (q = 3 → Even n)})
        (𝓝 (∫ ω, f (brownianMap (standardExcursion B ω) (fun t => Z t ω)) ∂P)) := by sorry

end LeGallBrownianMap
