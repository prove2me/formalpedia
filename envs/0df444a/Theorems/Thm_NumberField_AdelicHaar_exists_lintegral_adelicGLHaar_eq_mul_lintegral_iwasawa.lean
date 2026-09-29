-- Prove2me | Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
-- name    : NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d734bac0-f1fd-5efa-b6ad-bad7b5e9d449
-- title:
--   Haar measure on GL₂(A_K) in Iwasawa coordinates
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A}_K$ and $\mathrm{GL}_2(\mathbb{A}_K)$ the group `AdelicGL2 (𝓞 K) K` of invertible $2\times 2$ matrices over $\mathbb{A}_K$, both equipped with the Borel $\sigma$-algebras of their topologies. The assertion is that there is a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every measurable $\varphi \colon \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$ the lower Lebesgue integral of $\varphi$ against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` of $\mathrm{GL}_2(\mathbb{A}_K)$ equals $c$ times the iterated integral, innermost over $k$ against `maximalCompactHaar K` (the measure `Measure.haarMeasure ⊤` on the subgroup `adelicMaximalCompact K` of those $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` and whose archimedean component at every infinite place $w$ of $K$ is a row isometry), then over $t$ against the Haar measure [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391) of $\mathbb{A}_K^\times$, then over $u$ against the same measure, and outermost over $x$ against the additive Haar measure `adelicAddHaar (𝓞 K) K` of $\mathbb{A}_K$, of
--   $$\varphi\bigl(n(x)\, z(u)\, a(t)\, k\bigr)\cdot \mathrm{ofReal}\bigl(\lVert t\rVert^{-1}\bigr),$$
--   where $n(x)$ is the unipotent matrix $\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)$, $z(u)$ is the scalar matrix with entry $u$, $a(t)$ is $\mathrm{diag}(t,1)$, $k$ is viewed in $\mathrm{GL}_2(\mathbb{A}_K)$, and $\lVert t\rVert$ is the idelic norm [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19), the real number attached to $t$ by the distributive Haar character of $\mathbb{A}_K$.
--
--   This is the factorisation of Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ along the Iwasawa decomposition $g = n(x) z(u) a(t) k$, the adelic counterpart of $dg = dx\, d^\times u\, \lVert t\rVert^{-1} d^\times t\, dk$ on the Borel subgroup times the standard maximal compact subgroup, stated for nonnegative measurable functions and with an unspecified positive finite normalising constant. It is the measure-theoretic input for the computations of adelic integrals of automorphic forms on $\mathrm{GL}_2$ in this development, such as the evaluation of constant terms and of integrals in Iwasawa coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K) := by sorry
