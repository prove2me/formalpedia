-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinPairCore
-- name    : LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one_of_artinPairCore
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/12aba364-db7f-5697-8eba-d4c63c7e36c4
-- title:
--   Artin reciprocity for the cyclic octic layer L/K'
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, equipped with a group isomorphism $e:\mathrm{Gal}(L/\mathbb{Q})\xrightarrow{\sim}\mathrm{GL}_2(\mathbb{Z}/3)$, and let $K'$ be the fixed field of the subgroup `c8H e` of elements whose image under $e$ is the reduction of a matrix in `C8`, with $\mathrm{Gal}(L/K')$ assumed commutative. Fix $\zeta\in\mathbb{C}$ with $\zeta^4=-1$, an ideal $\mathfrak{f}\neq 0$ of $\mathcal{O}_{K'}$, and $\sigma\in\mathrm{Gal}(L/K')$ such that every element lies in the integral powers of $\sigma$. Assume given: for each $i$ in `primeCarriers` $K'\,\mathfrak{f}$ (the classes of primes $v\nmid\mathfrak{f}$) an `ArtinFieldCore` datum $D_i$, consisting of a tower $K'\subseteq E_i\subseteq N_i\subseteq\Theta_i$ with $N_i/E_i$ and $\Theta_i/E_i$ abelian, $\Theta_i=E_i(\zeta_{q_i})$, a modulus $\mathfrak{m}_i$ of $K'$ divisible by $\mathfrak{f}$ with $(q_i)\mid\mathfrak{m}_i\mathcal{O}_{E_i}$, a place $v_i$ in the class $i$ coprime to $\mathfrak{m}_i$ and a prime $w_i$ of $E_i$ above it of inertia degree one; and for each pair $i,j$ an `ArtinPairCore` datum $P_{ij}$ over $\sigma$, giving a tower $K'\subseteq E''_{ij}\subseteq N''_{ij}$ with $N''_{ij}/E''_{ij}$ abelian, a common modulus $\mathfrak{m}''_{ij}$ divisible by $\mathfrak{f}$, $\mathfrak{m}_i$ and $\mathfrak{m}_j$, admissibility of $\mathfrak{m}''_{ij}\mathcal{O}_{E''_{ij}}$ for $N''_{ij}/E''_{ij}$, compatibility of the Artin symbols of $L/K'$ and $N''_{ij}/E''_{ij}$ under the relative norm on classes coprime to the modulus, and injectivity of the restriction map together with $\sigma$ lying in its range. Assume further an ideal $\mathfrak{f}_0$ of $\mathbb{Z}$ which is an admissible modulus for $L/\mathbb{Q}$ (nonzero, and divisible by $v^{\mathrm{admissibleExp}}$ for every $v$ with nontrivial inertia in $L$) with $\mathfrak{f}_0\mathcal{O}_{K'}\mid\mathfrak{f}$. The remaining hypotheses are the two index inequalities: second-inequality bounds `hH1_i` and `hH1`, asserting that inside the group of fractional-ideal classes coprime to the relevant modulus, the index of the join of the narrow ray subgroup with the image of the relative norm homomorphism (the `raySymbolUnitsHom` built from $w\mapsto\mathfrak{p}_{w\cap E}^{f(w)}$) divides $|\mathrm{Gal}(N_i/E_i)|$, resp. $|\mathrm{Gal}(L/K')|$; and first-inequality data `hdata_i`, `hdata_ij` for every intermediate field of prime degree in $N_i/E_i$, resp. $N''_{ij}/E''_{ij}$, together with `hdata` for $L/K'$ and $\mathfrak{f}$, each asserting the existence of a norm homomorphism on idele unit groups compatible with adjusters and with the content homomorphism, containing the unit ideles in its range when the modulus is admissible, and whose join with the principal ideles has index divisible by the degree. Then for every $\alpha\in\mathcal{O}_{K'}$ with $\alpha\neq 0$, $\alpha-1\in\mathfrak{f}$ and $\tau(\alpha)>0$ for every real embedding $\tau$ of $K'$, the ray symbol $\prod_v(\mathrm{artinValue}\, e\, h\zeta\,v)^{\mathrm{ord}_v(\alpha)}$ of the principal fractional ideal $(\alpha)$ equals $1$ in $\mathbb{C}^\times$, where `artinValue e hζ` $v$ is the value of the character `chiGal e hζ` at the Frobenius seed `seedFrob (c8H e) v`.
--
--   This is Artin's reciprocity law for the cyclic degree-$8$ extension $L/K'$ inside a $\mathrm{GL}_2(\mathbb{F}_3)$-extension of $\mathbb{Q}$, in its ideal-theoretic form: the character-valued ray symbol is trivial on totally positive principal ideals congruent to $1$ modulo $\mathfrak{f}$. The crossing argument with cyclotomic fields is carried out in `raySymbol_artinValue_span_eq_one_of_artinFieldCore`, with the two index inequalities of class field theory entering as hypotheses rather than being proved here; the present form feeds into `raySymbol_artinValue_span_eq_one`, where the auxiliary data are constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinPairCore.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_LanglandsTunnell_C8Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2 LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one_of_artinPairCore
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    [IsMulCommutative (L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)]
    {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (𝔣 : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)))
    (σ : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)
    (hσ : ∀ g : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L, g ∈ Subgroup.zpowers σ)
    (D : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ArtinFieldCore (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣 i)
    (P : ∀ i j : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ArtinPairCore (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣 σ (D i) (D j))
    {𝔣₀ : Ideal (𝓞 ℚ)} (h0 : IsAdmissibleModulus ℚ L 𝔣₀)
    (hdiv : modulusExt ℚ (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣₀ ∣ 𝔣)
    (h𝔣 : 𝔣 ≠ ⊥)
    (hH1_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣),
      ((narrowRaySubgroup (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)).subgroupOf (coprimeToModulus (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)) ⊔
          ((coprimeToModulus (D i).N (((modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)).map (algebraMap (𝓞 (D i).E) (𝓞 (D i).N)))).map
            (raySymbolUnitsHom (D i).N (fun w : HeightOneSpectrum (𝓞 (D i).N) =>
              primeUnit (D i).E (w.under (𝓞 (D i).E)) ^ ((w.under (𝓞 (D i).E)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))).index ∣ Nat.card ((D i).N ≃ₐ[(D i).E] (D i).N))
    (hH1 :
      ((narrowRaySubgroup (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣).subgroupOf (coprimeToModulus (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣) ⊔
          ((coprimeToModulus L ((𝔣).map (algebraMap (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (𝓞 L)))).map
            (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
              primeUnit (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) ^ ((w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣)).index ∣ Nat.card (L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L))
    (hdata_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ∀ F : IntermediateField (D i).E (D i).N,
      (Module.finrank (D i).E F).Prime →
      IdeleFirstIneqData (D i).E (D i).N F (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))
    (hdata_ij : ∀ i j : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ∀ F : IntermediateField (P i j).E'' (P i j).N'',
      (Module.finrank (P i j).E'' F).Prime →
      IdeleFirstIneqData (P i j).E'' (P i j).N'' F (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (P i j).E'' (P i j).𝔪''))
    (hdata : IdeleFirstIneqDataAt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣)
    (α : 𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hαpos : ∀ τ : (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) →+* ℝ, 0 < τ (algebraMap (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) α)) :
    raySymbol (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (artinValue e hζ)
        ((Ideal.span {α} : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : FractionalIdeal ((𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))⁰) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) = 1 := by sorry
