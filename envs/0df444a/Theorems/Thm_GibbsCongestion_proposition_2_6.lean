-- Prove2me | Theorems.Thm_GibbsCongestion_proposition_2_6
-- name    : GibbsCongestion.proposition_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:02:19.977783+00:00
-- url     : https://prove2.me/theorems/a8eb92bc-1428-41a5-b0fd-eb8c852c2843
-- title:
--   Proposition 2.6 (Brändén and Huh): M-concave log-weights give an SLC generating polynomial
-- statement:
--   Let $\kappa\in\mathbb Z^n_{\ge0}$, $K=\prod_i\{0,\dots,\kappa_i\}$, and $w:K\to\mathbb R_{\ge0}$ a non-negative weight function. Consider
--   $$g_\kappa(x)=\sum_{\alpha\in K}\frac{w(\alpha)}{\alpha!}x^\alpha,\qquad(6)$$
--   and assume that $g_\kappa$ is $d$-homogeneous. Let $\nu:\mathbb Z^n_{\ge0}\to\mathbb R\cup\{-\infty\}$ be $\nu(\alpha)=\log w(\alpha)$ for $\alpha\in K$ (with $\log0=-\infty$) and $\nu(\alpha)=-\infty$ otherwise. If $\nu$ is M-concave, then $g_\kappa$ is strongly log-concave.
--
--   Applied to $w(\alpha)=e^{-T\Phi(\alpha)}$ on load profiles it yields Lemma 4.3.
--
--   **Formalization Note** $\nu$ is M-concave iff $-\nu$ is M-convex; $-\nu$ is passed to Murota's exchange axiom on $\mathbb Z^n$ with value $+\infty$ outside $K$ and where $w=0$. The weight is given on all of $\mathbb N^n$ and only its values on $K$ enter.
--
--   Differences from the source:
--   - reading: log-concave on a subset S ⊆ ℝⁿ≥0 (S unspecified) → log-concave on the open positive orthant; reason: the convention of the cited works (Anari et al.; Brändén–Huh)
--   - encoding: ν M-concave (M♯-concave exchange (5) plus dom ν in a hyperplane) → MExchangeAxiom of −ν, with ⊤ for −∞; reason: M-EXC with a nonempty domain implies the hyperplane condition; with an empty domain both hold
--   - encoding: a weight function w on K with values in ℝ≥0 → a total function w on ℕ-vectors, non-negative on K; reason: values off K enter neither g_κ nor ν
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.6, display (6), p.10; M-concavity, §2.2, p.9

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_GibbsCongestion_IsSLC

namespace GibbsCongestion

/-- **Proposition 2.6** (Brändén and Huh) (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.6, p.10). Let `κ ∈ ℤ^σ_{≥0}`,
`K = ∏_i {0, …, κ_i}`, `w : K → ℝ_{≥0}`, and `g_κ(x) = ∑_{α ∈ K} (w(α)/α!) x^α` (6), assumed
`d`-homogeneous. Let `ν(α) = log w(α)` for `α ∈ K` (with `log 0 = −∞`) and `ν(α) = −∞` otherwise.
If `ν` is M-concave, then `g_κ` is strongly log-concave.

**Formalization Note** `ν` is M-concave iff `−ν` is M-convex; `−ν` is passed to Murota's exchange
axiom M-EXC[ℤ] on `ℤ^σ` with value `+∞` outside `K` and where `w = 0`. The weight is a function on
all of `σ → ℕ` and only its values on `K` matter. -/
theorem proposition_2_6 {σ : Type*} [Fintype σ] [DecidableEq σ] (κ : σ → ℕ) (w : (σ → ℕ) → ℝ)
    (hw : ∀ α ∈ Fintype.piFinset (fun i => Finset.range (κ i + 1)), 0 ≤ w α) (d : ℕ)
    (hhom : (∑ α ∈ Fintype.piFinset (fun i => Finset.range (κ i + 1)),
        MvPolynomial.C (w α / ∏ i, ((α i).factorial : ℝ)) * ∏ i, MvPolynomial.X i ^ α i).IsHomogeneous d)
    (hM : DiscreteConvex.ConjugacyDualityD.MExchangeAxiom (fun β : σ → ℤ =>
      if (∀ i, 0 ≤ β i ∧ β i ≤ (κ i : ℤ)) ∧ 0 < w (fun i => (β i).toNat) then
        ((-Real.log (w (fun i => (β i).toNat)) : ℝ) : WithTop ℝ)
      else ⊤)) :
    IsSLC (∑ α ∈ Fintype.piFinset (fun i => Finset.range (κ i + 1)),
      MvPolynomial.C (w α / ∏ i, ((α i).factorial : ℝ)) * ∏ i, MvPolynomial.X i ^ α i) := by sorry

end GibbsCongestion
