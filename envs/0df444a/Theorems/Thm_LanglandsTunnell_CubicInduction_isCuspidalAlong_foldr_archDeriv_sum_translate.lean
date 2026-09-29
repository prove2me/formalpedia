-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_foldr_archDeriv_sum_translate
-- name    : LanglandsTunnell.CubicInduction.isCuspidalAlong_foldr_archDeriv_sum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4e9aaddc-8c15-5f3c-b56e-e5715c982aa1
-- title:
--   Derivative words of translates stay cuspidal along both parabolics
-- statement:
--   Let $f : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be continuous and of moderate growth, in the sense that $\|f(g)\| \le C\,\mathrm{gauge3}_{\mathbb{Q}}(g)^N$ for some constant $C$ and exponent $N$ and all $g$. Fix the carrier pins `productionPinsOf` over $\mathbb{Q}$ with empty region, trivial level subgroups, trivial uniformisers and box the adelic box (infinite box times integral finite adeles), so that the relevant additive measure $\nu$ is adelic additive Haar measure conditioned on that box. Assume $f$ is cuspidal along $P_{2,1}$ and along $P_{1,2}$ for these pins, i.e. $\int\!\int f(\mathrm{radicalP21}\,[x,y]\cdot g)\,d\nu\,d\nu = 0$ and likewise with $\mathrm{radicalP12}$, for every $g$. Assume further that $f$ is archimedean-smooth, i.e. for each $g$ the map $e \mapsto f(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the set of real $3\times 3$ matrices of nonzero determinant, and that there is a finite set $s$ of functions with $g \mapsto f(gk)$ in the $\mathbb{C}$-span of $s$ for every $k$ with all finite components $1$ and archimedean component in $\mathrm{orth3} = \{k : k^{\mathsf T}k = 1\}$. Let $c : \mathrm{Fin}\,n \to \mathbb{C}$ and $t : \mathrm{Fin}\,n \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with each $t_i$ trivial at the archimedean place, and suppose $v := x \mapsto \sum_i c_i f(x t_i)$ is centre-finite, i.e. for each of the three operators $\mathrm{casimir1}, \mathrm{casimir2}, \mathrm{casimir3}$ there are $N$ and coefficients $a$ with $a(\mathrm{Fin.last}\,N) = 1$ and $\sum_m a_m \cdot (\text{operator}^{[m]} v) = 0$. Then for every word $w$ of pairs in $\mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, the function obtained from $v$ by applying the archimedean derivatives $\mathrm{archDeriv}\,i\,j$ (differentiation at $s = 0$ of the right translate by $\mathrm{archRealLift3}(1 + sE_{ij})$) along $w$ via `List.foldr` is again cuspidal along $P_{2,1}$ and along $P_{1,2}$ for the same pins.
--
--   This is the stability of cusp forms on $\mathrm{GL}_3$ under right translation and under the action of right-invariant archimedean differential operators, in the concrete form needed here: vanishing of the two constant terms along the unipotent radicals of the maximal parabolics persists after passing to a finite combination of translates and applying any word of archimedean derivatives. It feeds the construction of Whittaker data in the cubic induction, being cited in the production of ray-order bounds for derivative words and in the assembly of the seed package from elements of the span of archimedean derivatives of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_foldr_archDeriv_sum_translate.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.isCuspidalAlong_foldr_archDeriv_sum_translate
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite (fun x => ∑ i, c i * f (x * t i)))
    (w : List (Fin 3 × Fin 3)) :
    IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w) ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w) := by sorry
