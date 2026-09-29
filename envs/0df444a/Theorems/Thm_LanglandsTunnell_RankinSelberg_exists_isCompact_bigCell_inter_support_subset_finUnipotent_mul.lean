-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
-- name    : LanglandsTunnell.RankinSelberg.exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4a233aae-f9c9-54e6-9dfb-6e850a59a68f
-- title:
--   Big-cell support of W· F inside N· K'
-- statement:
--   Fix a finite set $S$ of nonzero primes of $\mathcal O_{\mathbb Q}$, and two functions $W,F$ on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ with values in $\mathbb C$. All group elements below range over `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection [`NumberField.AdelicLevel.glArch`](def/NumberField_AdelicLevel.html#L191), and for a prime $v$, `localAt ℚ v` denotes the $v$-component homomorphism $\mathrm{GL}_2(\mathbb A_{\mathbb Q})\to\mathrm{GL}_2(\mathbb Q_v)$. Call $g$ big-cell if for every $v\notin S$ the component `localAt ℚ v g` factors as $n\,k$ with $n$ in the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over $\mathbb Q_v$, i.e. a matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of the subgroup of matrices over the finite adeles that are level-one for the ideal $\top$ together with their inverses. The hypothesis asserts the existence of a compact set $\mathrm{Cpt}$ and a real $B_0$ such that $\|W(g)F(g)\|\le B_0$ for all $g$, and such that every big-cell $g$ with $W(g)F(g)\neq 0$ admits $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) (the range of `unipotentGL2Hom` over $\mathbb A_{\mathbb Q}$, intersected with the finite-adelic subgroup) and $h\in\mathrm{Cpt}$ with `localAt ℚ v (n * g) = localAt ℚ v h` for all $v\in S$. The conclusion: there is a compact $K'$ such that the set of big-cell $g$ with $W(g)F(g)\neq 0$ is contained in the pointwise product [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) $\cdot\,K'$.
--
--   This is the adelic half of the cell-finiteness step in the Rankin–Selberg estimates: the hypothesis controls the components at the finitely many places of $S$ modulo the unipotent subgroup, and the conclusion upgrades this to a global containment of the support of $W\cdot F$ on the big cell in a set of the form $N(\mathbb A_{\mathbb Q,f})\cdot K'$ with $K'$ compact. It relies on the compactness of the level-one subgroup intersected with the finite-adelic subgroup ([`AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup`](thm.html#AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup)), and is used in the integrability statements for the Rankin–Selberg integrand, in particular [`LanglandsTunnell.RankinSelberg.lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support`](thm.html#LanglandsTunnell.RankinSelberg.lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

open scoped Pointwise

theorem LanglandsTunnell.RankinSelberg.exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hsupp : ∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, ‖W g * F g‖ ≤ B₀) ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
            ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
        W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
            ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
              localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) :
    ∃ K' : Set (finiteAdelicGL2Subgroup ℚ), IsCompact K' ∧
      {g : finiteAdelicGL2Subgroup ℚ |
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k) ∧ W g * F g ≠ 0} ⊆
        ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) * K' := by sorry
