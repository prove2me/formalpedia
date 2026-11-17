-- Prove2me | Theorems.Thm_NNPartTree_Supplement_theorem_5
-- name    : NNPartTree.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:11:54.153577+00:00
-- url     : https://prove2.me/theorems/cb34227e-aad3-48a3-878b-0e64df3b630b
-- title:
--   Theorem 5 — Gaussian-like marginals give the $(R,J)$-halfspace approximation degree bound
-- statement:
--   Let $L, B > 0$. A distribution on $\mathbb{R}^d$ is $(L, 0)$-anticoncentrated and $B$-subgaussian in the sense of Definition B.1. A function $h : \mathbb{R}^d \to \{-1, 1\}$ is an $(R, J)$-halfspace function if $\{h = 1\}$ is a disjoint union of $R$ intersections of $J$ halfspaces (Definition 6.4). A distribution $\mathcal{D}$ on pairs has $(R, J)$-halfspace approximation degree $k(\varepsilon; R, J; \mathcal D) \le k$ if every $(R, J)$-halfspace function $h$ has a polynomial $A$ of total degree at most $k$ with
--   $$\mathbb{E}_{x \sim \mathcal D_X}|A(x) - h(x)|^\ell \le \varepsilon \quad\text{and}\quad \mathbb{E}_{y \sim \mathcal D_Y}|A(y) - h(y)|^\ell \le \varepsilon \qquad (\ell \in \{1, 2, 4\})$$
--   (Definitions 5.1 and 6.7).
--
--   **Theorem.** There are constants $c_1 > 0$, $C$ and $K$, depending only on $L$ and $B$, such that the following holds for every dimension $d$. Let $\mathcal{M}$ be an $(L, 0)$-anticoncentrated, $B$-subgaussian probability distribution on $\mathbb{R}^d$, let $\varepsilon, \delta \in (0, 1)$, let $R, J \in \mathbb{N}$, and let
--   $$m \ge C\,\big(1 + d + 1/\varepsilon + \log(1/\delta) + R + 2^J\big)^K.$$
--   Then, with probability at least $1 - \delta$ over a dataset $\mathbf{P} \sim \mathcal{M}^m$, every distribution $\mathcal{D}$ on $\mathbb{R}^d \times \mathbb{R}^d$ whose first marginal $\mathcal{D}_X$ is $(L, 0)$-anticoncentrated and $B$-subgaussian and whose second marginal $\mathcal{D}_Y$ is the uniform distribution over $\mathbf{P}$ satisfies
--   $$k(\varepsilon; R, J; \mathcal D) \le \left(\frac{R \cdot 2^J}{\varepsilon}\right)^{c_1}.$$
--
--   This is the paper's justification of the first hypothesis of its main theorem (Theorem 4): nearest neighbor distributions with Gaussian-like queries and a dataset drawn from a Gaussian-like distribution satisfy the polynomial approximation degree bound, with high probability over the dataset.
--
--   **Formalization Note** The event over $\mathbf{P}$ is a measurable set $G$ of datasets with $\mathcal{M}^m(G) \ge 1 - \delta$. Moments are lower integrals, so a polynomial with infinite moments does not qualify. The degree bound is compared in $\mathbb{R}$ with a real power.
--
--   Differences from the source:
--   - reading: "constants" c₁ and poly(·), stated after the assumptions on D and M → c₁, C, K depend only on L and B and are chosen before d, M, ε, δ, R, J; reason: the theorem calls them constants and fixes only L, B as constants; this is the stronger reading
--   - encoding: m ≥ poly(d, 1/ε, log(1/δ), R, 2^J) → m ≥ C (1 + d + 1/ε + log(1/δ) + R + 2^J)^K for some C, K; reason: every polynomial in these nonnegative quantities is bounded by an expression of this form, and every such expression is a polynomial
--   - reading: a distribution D whose second marginal is the uniform distribution over the random dataset P → every probability measure D with the stated marginals, quantified inside the event over P; reason: D depends on P, so it cannot be fixed before the draw; quantifying every such D is the strongest reading
--   - reading: δ is not quantified in print → every δ ∈ (0, 1); reason: log(1/δ) and "probability at least 1 − δ" are meaningful exactly for δ ∈ (0, 1)
--   - encoding: "with probability at least 1 − δ over the draw of P" → a measurable set G of datasets with M^m(G) ≥ 1 − δ on which the conclusion holds; reason: standard meaning of a high-probability event
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 5, p.34 (PDF p.34); Definition B.1, p.34; Definition 6.7, p.26 (PDF p.26)

import Mathlib
import Definitions.Def_NNPartTree_Moments
import Definitions.Def_NNPartTree_Supplement_Anticoncentrated

set_option autoImplicit false

namespace NNPartTree.Supplement

open MeasureTheory

/-- **Theorem 5** (Gaussian-like marginals give the degree bound) (Khanna–Padaki–Waingarten,
*Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909, held copy of 2026-11-03,
sha256 d32992f2…, Theorem 5, p.34, PDF p.34; Definitions B.1, p.34, and 6.7, p.26).
Let `L, B > 0`. There are a constant `c₁ > 0` and a polynomial bound `C (1 + d + 1/ε + log(1/δ) + R +
2^J)^K` such that the following holds. Let `M` be an `(L, 0)`-anticoncentrated, `B`-subgaussian
distribution on `ℝᵈ`, let `ε, δ ∈ (0, 1)`, `R, J ∈ ℕ`, and let `m` be at least the bound. Then with
probability at least `1 − δ` over a dataset `P ∼ M^m`, every distribution `D` on `ℝᵈ × ℝᵈ` whose first
marginal `D_X` is `(L, 0)`-anticoncentrated and `B`-subgaussian and whose second marginal `D_Y` is the
uniform distribution over `P` has `(R, J)`-halfspace approximation degree `k(ε; R, J; D) ≤
(R · 2^J/ε)^{c₁}`: every `(R, J)`-halfspace function `h` has a polynomial `A` of total degree at most
`(R · 2^J/ε)^{c₁}` with `E|A − h|^ℓ ≤ ε` under both marginals for `ℓ ∈ {1, 2, 4}`.

**Formalization Note** `c₁`, `C` and `K` depend on `L` and `B` only. Every polynomial in
`d, 1/ε, log(1/δ), R, 2^J` is dominated by `C (1 + d + 1/ε + log(1/δ) + R + 2^J)^K`, so the threshold
is the printed `poly(·)`. The event is a measurable set `G` of datasets with `P^m(G) ≥ 1 − δ`; `D`
depends on `P`, so it is quantified inside the event. Moments are lower integrals (`MomentBound`). -/
theorem theorem_5 (L B : ℝ) (hL : 0 < L) (hB : 0 < B) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ (C : ℝ) (K : ℕ),
      ∀ (d : ℕ) (M : Measure (Pt d)), IsProbabilityMeasure M →
        Anticoncentrated M L 0 → Subgaussian M B →
        ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ (R J m : ℕ),
          C * (1 + d + 1 / ε + Real.log (1 / δ) + R + 2 ^ J) ^ K ≤ (m : ℝ) →
          ∃ G : Set (Fin m → Pt d), MeasurableSet G ∧
            1 - δ ≤ (Measure.pi (fun _ : Fin m => M) G).toReal ∧
            ∀ P ∈ G, ∀ D : Measure (Pt d × Pt d), IsProbabilityMeasure D →
              marginalY D = datasetLaw P →
              Anticoncentrated (marginalX D) L 0 → Subgaussian (marginalX D) B →
              ∀ h : Pt d → ℝ, IsRJFunction R J h →
                ∃ A : MvPolynomial (Fin d) ℝ,
                  (A.totalDegree : ℝ) ≤ ((R : ℝ) * 2 ^ J / ε) ^ c₁ ∧
                    MomentBound D h A ε := by sorry

end NNPartTree.Supplement
