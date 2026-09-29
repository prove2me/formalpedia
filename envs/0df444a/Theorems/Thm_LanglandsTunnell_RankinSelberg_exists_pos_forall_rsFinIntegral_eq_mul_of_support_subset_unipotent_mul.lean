-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/eadb980c-8c1e-5dae-a99f-774284ff25a2
-- title:
--   Unipotent-compact bump: finite Rankin–Selberg integral is c W(1)F(1)
-- statement:
--   Work with $G =$ `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch` on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and with $N =$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the intersection with $G$ of the range of the unipotent embedding into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$. Assume the ambient group $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ is second countable (its Borel structure coming from `glBorel`), let $\mu$ be a Haar measure on $G$ and $\mu_N$ a Haar measure on $N$, and let $U \le G$ be a subgroup that is compact and open as a subset of $G$ and satisfies $\mathrm{ideleNorm}_{\mathbb{Q}}(\det u) = 1$ for every $u \in U$, where `ideleNorm` is the value of the distributive Haar character of the adele ring. Then there exists a real $c > 0$ such that for every $s \in \mathbb{C}$ and every pair of functions $W, F : G \to \mathbb{C}$ for which (i) the product satisfies $W(ng)F(ng) = W(g)F(g)$ for all $n \in N$, $g \in G$, (ii) $W(g)F(g) \neq 0$ forces $g = nu$ for some $n \in N$ and $u \in U$, and (iii) $W(u)F(u) = W(1)F(1)$ for all $u \in U$, one has
--   $$\int_G W(g)F(g)\,\bigl(\mathrm{ideleNorm}_{\mathbb{Q}}(\det g)\bigr)^{s - 1/2}\,d\bigl(\mu \cdot \mathrm{density}(N,\mu_N)\bigr)(g) \;=\; c \cdot W(1)F(1),$$
--   that is, [`RSCarrier.rsFinIntegral μ μN s W F`](def/LanglandsTunnell_RSCarrier.html#L46) $= c\,(W(1)F(1))$, the integral being taken against $\mu$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N$ and $\mu_N$. The constant $c$ depends only on $\mu$, $\mu_N$ and $U$, and in particular not on $s$, $W$ or $F$.
--
--   This is the finite-adelic form of the evaluation of a Rankin–Selberg integral at a bump test vector: when the product $W\cdot F$ is left invariant under the unipotent subgroup, supported on a single coset region $N\cdot U$ with $U$ compact open of trivial determinant norm, and constant on $U$, the integral degenerates into a positive measure constant times the value at the identity, with no dependence on the spectral parameter $s$. It feeds the computation of the Rankin–Selberg cells and dual constant in the $\mathrm{GL}_3$-translate statement used in the Langlands–Tunnell part of the argument; the only input cited is the quotient integral formula [`HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out`](thm.html#HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out) for a closed subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open NumberField.TateGlobal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (U : Subgroup (finiteAdelicGL2Subgroup ℚ))
    (hUc : IsCompact (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUo : IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUdet : ∀ u ∈ U, ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((u : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : finiteAdelicGL2Subgroup ℚ → ℂ),
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          W ((n : finiteAdelicGL2Subgroup ℚ) * g) * F ((n : finiteAdelicGL2Subgroup ℚ) * g) = W g * F g) →
        (∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U ∧
            g = (n : finiteAdelicGL2Subgroup ℚ) * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsFinIntegral μ μN s W F = (c : ℂ) * (W 1 * F 1) := by sorry
