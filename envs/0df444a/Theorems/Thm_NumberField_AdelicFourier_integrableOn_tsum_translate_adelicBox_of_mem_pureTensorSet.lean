-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet
-- name    : NumberField.AdelicFourier.integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/0407a626-3b07-5f96-b809-f6daefff819a
-- title:
--   Integrability of the periodisation of a pure tensor on A_F
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite over $\mathbb{Q}$, in the universe of types `Type`), and let $\Phi : \mathbb{A}_F \to \mathbb{C}$ be a function on the adele ring $\mathbb{A}_F = \mathrm{AdeleRing}(\mathcal{O}_F, F)$, viewed as the product of the infinite adeles and the finite adeles. Assume $\Phi$ belongs to `pureTensorSet F`, that is: there are a Schwartz function $g$ on the mixed space $\mathrm{mixedSpace}\,F$ of $F$ and a function $h$ on the finite adele ring $\mathbb{A}_{F,\mathrm{fin}}$ which is locally constant and has compact support, such that $\Phi(x) = g(\rho(x_\infty))\, h(x_{\mathrm{fin}})$ for all $x$, where $\rho$ is the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F` from the infinite adeles to the mixed space. The conclusion is that the periodisation $t \mapsto \sum_{\xi \in F}' \Phi(t + \iota\xi)$, where $\iota$ is the structure map $F \to \mathbb{A}_F$ and the sum is Lean's unconditional `tsum` over all $\xi \in F$ (hence $0$ at points where the family is not summable), is integrable over the adelic box `adelicBox F` with respect to the additive Haar measure `adelicAddHaar (𝓞 F) F` on $\mathbb{A}_F$ for its Borel $\sigma$-algebra. Here `adelicBox F` consists of those $x$ whose infinite component is carried by $\rho$ into the fundamental domain of the $\mathbb{Z}$-span of the lattice basis `mixedEmbedding.latticeBasis F`, and whose finite component satisfies $x_v \in \mathcal{O}_{F_v}$ at every finite place $v$.
--
--   This is the integrability hypothesis needed for Poisson summation on $\mathbb{A}_F$ in the style of Tate's thesis: the adelic box is a fundamental domain for the principal adeles, and the periodisation of a Schwartz–Bruhat pure tensor is integrable over it. It is used in the estimates on the Borel part of the adelic kernel minus its constant term, whose unipotent slices are pure tensors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicHaar

theorem NumberField.AdelicFourier.integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet (F : Type) [Field F] [NumberField F]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Φ ∈ pureTensorSet F) :
    MeasureTheory.IntegrableOn (fun t => ∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
      (adelicBox F) (adelicAddHaar (𝓞 F) F) := by sorry
