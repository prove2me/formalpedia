-- Prove2me | Theorems.Thm_Hairer_reconstruction_approximants_cauchy_controlled
-- name    : Hairer.reconstruction_approximants_cauchy_controlled
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T05:46:17.423136+00:00
-- url     : https://prove2.me/theorems/148f87d9-0a41-4817-964e-660915c06812
-- title:
--   Consistency of reconstruction approximants with coefficient control in Hairer's regularity structures
-- statement:
--   Consistency of the reconstruction approximants with coefficient control (key estimate of Hairer 2014, Section 3.1). For a regularity structure with model $(\\Pi, \\Gamma)$, least homogeneity $\\alpha < 0$, $\\gamma > 0$, and a modelled distribution $f \\in \\mathcal{D}^\\gamma$, the atomic approximants are consistent under coefficient control: any two atomic decompositions $\\varphi = \\sum_i c_i S^\\delta_{s,x_i}\\eta_i$ and $\\varphi = \\sum_j c'_j S^{\\delta'}_{s,x'_j}\\eta'_j$ of the same test function $\\varphi$ at scales $\\delta, \\delta' \\in (0,1]$, with all atoms supported in a fixed compact $K$ and coefficients satisfying $\\sum_i |c_i| \\le M$, $\\sum_j |c'_j| \\le M$, give approximant values differing by at most $$ \\left|\\sum_i c_i \\langle \\Pi_{x_i}f(x_i), S^\\delta_{s,x_i}\\eta_i\\rangle - \\sum_j c'_j \\langle \\Pi_{x'_j}f(x'_j), S^{\\delta'}_{s,x'_j}\\eta'_j\\rangle\\right| \\le C(\\varphi, K, M)\\,\\max(\\delta,\\delta')^\\gamma. $$ Hence the approximants form a Cauchy net as $\\delta \\to 0$ and the limit is independent of the chosen decompositions. This is the analytic core of Hairer's reconstruction theorem (Theorem 3.10); the proof is the multiresolution estimate of Section 3.1. Formalization Note: this statement repairs the earlier published `Hairer.reconstruction_approximants_cauchy`, which quantified over arbitrary atomic decompositions with no coefficient control; the standard recentring proof needs the bounds $\\sum_i|c_i| \\le M$ and atom support in a compact $K$, matching the guarantees of the proved decomposition theorem `Hairer.testFunction_decomposition_scaledTest`. The constant $C$ is explicitly allowed to depend on the control data $K, M$.
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), 269-504, arXiv:1303.5113, Section 3.1.

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Consistency of reconstruction approximants, with coefficient control
(Hairer 2014, §3.1, key estimate).**

For `f ∈ D^γ` with `γ > 0`, the atomic approximants built from the model's germs
are consistent: evaluating the approximant
`∑ᵢ cᵢ ⟨Π_{xᵢ} f(xᵢ), S^δ_{s,xᵢ} ηᵢ⟩` on any two atomic decompositions
`φ = ∑ᵢ cᵢ S^δ_{s,xᵢ} ηᵢ` and `φ = ∑ⱼ c'ⱼ S^{δ'}_{s,x'ⱼ} η'ⱼ` of the same test
function `φ` at scales `δ, δ' ∈ (0,1]`, both with atoms supported in a fixed
compact `K` and coefficients satisfying `∑ᵢ |cᵢ| ≤ M`, gives values differing
by at most `C(φ,K,M)·max(δ,δ')^γ`. In particular the approximants form a Cauchy
net as `δ → 0`, and the limit is independent of the chosen decompositions.
This is the analytic core of the reconstruction theorem (Theorem 3.10); the
proof is Hairer's multiresolution estimate in §3.1.

This statement repairs `Hairer.reconstruction_approximants_cauchy` by adding the
coefficient hypotheses (`∑ᵢ |cᵢ| ≤ M` and atom support in a compact `K`),
matching the guarantees of the proved decomposition theorem
`Hairer.testFunction_decomposition_scaledTest`. -/
theorem reconstruction_approximants_cauchy_controlled
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d), ∀ (K : Set (Pt d)) (M : ℝ),
      IsCompact K →
      ∃ C : ℝ,
      ∀ (δ δ' : ℝ) (n n' : ℕ)
        (x : Fin n → Pt d) (c : Fin n → ℝ) (η : Fin n → (Pt d → ℝ))
        (x' : Fin n' → Pt d) (c' : Fin n' → ℝ) (η' : Fin n' → (Pt d → ℝ)),
        0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
        (∀ i, x i ∈ K) → (∀ i, x' i ∈ K) →
        (∑ i, |c i|) ≤ M → (∑ i, |c' i|) ≤ M →
        (∀ i, IsTestBall s r (η i)) → (∀ i, IsTestBall s r (η' i)) →
        (∀ y, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y) →
        (∀ y, φ y = ∑ i, c' i * scaledTest s δ' (x' i) (η' i) y) →
        |∑ i, c i * (Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
         - ∑ i, c' i * (Pi (x' i) (f (x' i))).eval (scaledTest s δ' (x' i) (η' i))|
          ≤ C * (max δ δ') ^ γ := by
  sorry

end Hairer
