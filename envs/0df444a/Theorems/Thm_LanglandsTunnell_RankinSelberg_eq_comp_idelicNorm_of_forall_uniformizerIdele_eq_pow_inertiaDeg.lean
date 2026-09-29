-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
-- name    : LanglandsTunnell.RankinSelberg.eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/8946ea61-33ef-5c54-b25a-ace3b5154ce2
-- title:
--   Rigidity of idele class characters over ℚ
-- statement:
--   Let $K$ be a number field. Let $\mu\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a continuous group homomorphism which is an idele class character, i.e. $\mu(\iota(u)) = 1$ for every $u \in K^\times$, where $\iota$ is the structure map $K \to \mathbb{A}_K$; let $\eta\colon \mathbb{A}_{\mathbb{Q}}^\times \to \mathbb{C}^\times$ be a continuous homomorphism that is likewise trivial on the principal ideles $\mathbb{Q}^\times$. For a maximal ideal $\mathfrak{P}$ of $\mathcal{O}_K$ write $\mathfrak{p} = \mathfrak{P} \cap \mathbb{Z}$ for the prime below it, and let $\varpi_{\mathfrak{P}}$ denote the uniformizer idele: the idele whose component at $\mathfrak{P}$ is the image in $K_{\mathfrak{P}}$ of the chosen uniformizer of $\mathfrak{P}$ and whose components at all other finite places and at the archimedean places are $1$. A character is unramified at a finite place $v$ when its local component at $v$, obtained by restricting along the embedding of $(K_v)^\times$ into the ideles at $v$, is trivial on all $t$ with both $t$ and $t^{-1}$ in the valuation ring. Assume that for every $\mathfrak{P}$ at which $\mu$ is unramified and such that $\eta$ is unramified at $\mathfrak{p}$, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{\mathfrak{p}})^{f(\mathfrak{P}/\mathfrak{p})}$ in $\mathbb{C}$, with $f(\mathfrak{P}/\mathfrak{p})$ the residue degree. Then $\mu$ equals the composite of the idelic norm $\mathbb{A}_K^\times \to \mathbb{A}_{\mathbb{Q}}^\times$ attached to the base change of adele rings along $\mathbb{Q} \to K$ — the map on units induced by the algebra norm of $\mathbb{A}_K$ over $\mathbb{A}_{\mathbb{Q}}$ — followed by $\eta$.
--
--   This is the multiplicity-one, or rigidity, statement for $\mathrm{GL}_1$: a continuous idele class character is determined by its values at the uniformizer ideles outside a finite set of places, so agreement with $\eta \circ N_{K/\mathbb{Q}}$ at the unramified uniformizers forces equality everywhere. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument to identify the central character of an automorphic representation with a base change of a character of $\mathbb{A}_{\mathbb{Q}}^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal
open M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.RankinSelberg.eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcμ : Continuous μ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η) (hcη : Continuous η)
    (h : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
      ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
        ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :
    μ = η.comp (genuineBaseChange ℚ K).idelicNorm := by sorry
