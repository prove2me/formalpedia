-- Prove2me | Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
-- name    : M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/8f2eadde-a036-5cfa-9633-03e10b06f2a8
-- title:
--   Kernel of the local component of the idelic Artin map
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E)$ commutative, and let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is an admissible modulus for the degree $n = [F:E]$, i.e. $\mathfrak f \neq 0$ and $v^{\,\mathrm{admissibleExpOfDegree}\,E\,n\,v} \mid \mathfrak f$ for every height-one prime $v$ of $\mathcal O_E$ whose inertia subgroup in $\mathrm{Gal}(F/E)$ at the chosen prime above $v$ is nontrivial. Let $r$ be a homomorphism from the idèle group $\mathbb{A}_E^\times$ to $\mathrm{Gal}(F/E)$ such that the principal idèles lie in $\ker r$; $\ker r$ equals the principal idèles joined with the image of the idelic norm attached to `genuineBaseChange E F`; $r$ is surjective; and $r(u) = \prod^{\mathrm f}_{v} \mathrm{artinFrob}(v)^{\mathrm{placeOrd}(u_{\mathrm{fin}},v)}$ for every $u$ satisfying `IsAdjuster E 𝔣 u 1` (valuation $1$ and $u - 1$ of valuation at most $\exp(-\mathrm{ord}_v\mathfrak f)$ at each $v \mid \mathfrak f$, and positive at every real embedding). Let $v$ be a height-one prime of $\mathcal O_E$, $a \in (E_v)^\times$, and $x$ an idèle with trivial infinite part and trivial component at every prime other than $v$, with component $a$ at $v$. Let $w$ be a height-one prime of $\mathcal O_F$ lying under $v$. Then $r(x) = 1$ if and only if there is $b \in (F_w)^\times$ with $\prod^{\mathrm f}_{\sigma \in D_w} \sigma \cdot b$ equal, in $F_w$, to the image of $a$ under the canonical semialgebra map $E_v \to F_w$, where $D_w$ is the decomposition subgroup of the valuation subring of $w$ in $\mathrm{Gal}(F/E)$.
--
--   This is the local norm theorem for the layer $F_w/E_v$ in idelic form: the local component of the idelic Artin map at $v$ is trivial exactly on the group of norms from $F_w^\times$, the norm being written as the product of the $D_w$-conjugates. It feeds the identification of the local component of $r$ with a local reciprocity map, the construction of adjusters realising prescribed elements of higher ramification groups, and the counting of places whose local norm group is proper.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField
open M4aHerbrand
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a)

    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    r x = 1 ↔
      ∃ b : (w.adicCompletion F)ˣ,
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            (a : v.adicCompletion E) := by sorry
