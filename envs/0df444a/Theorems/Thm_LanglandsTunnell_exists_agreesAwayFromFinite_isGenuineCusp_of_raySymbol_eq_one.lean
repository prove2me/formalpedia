-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
-- name    : LanglandsTunnell.exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/ea9eedb8-579f-5fb1-9fe4-4cb6495d7744
-- title:
--   Automorphic induction of a ray class character of E/F
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals, let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles of $F$, and let $E$ be a number field with an $F$-algebra structure such that $\mathrm{finrank}_F E = 2$. Let $\psi$ assign to each finite place of $E$ a unit of $\mathbb{C}$, and let $\mathfrak{f} \neq 0$ be an ideal of $\mathcal{O}_E$ such that for every non-zero $\alpha \in \mathcal{O}_E$ with $\alpha - 1 \in \mathfrak{f}$ and $\tau(\alpha) > 0$ for every real embedding $\tau$ of $E$, the symbol $\mathrm{raySymbol}\, E\, \psi$ of the fractional ideal $(\alpha)$, namely $\prod_{\mathfrak{P}} \psi(\mathfrak{P})^{\mathrm{ord}_{\mathfrak{P}}(\alpha)}$, equals $1$. Assume further that outside every finite set $S$ of finite places of $F$ there is a place $v \notin S$ carrying two distinct primes $\mathfrak{P}_1 \neq \mathfrak{P}_2$ of $E$ lying under to $v$ with $\psi(\mathfrak{P}_1) \neq \psi(\mathfrak{P}_2)$. Let $\Phi_0$ be a Hecke eigensystem over $F$ with coefficients in $\mathbb{Z}[\sqrt{-2}]$, that is, a non-zero level ideal of $\mathcal{O}_F$ together with functions $a, b$ on the finite places, such that for all $v$ outside some finite set: whenever $\mathfrak{P}_1 \neq \mathfrak{P}_2$ both lie under to $v$ one has $\iota(a(v)) = \psi(\mathfrak{P}_1) + \psi(\mathfrak{P}_2)$ and $\iota(b(v)) = \psi(\mathfrak{P}_1)\psi(\mathfrak{P}_2)$, and whenever $\mathfrak{P}$ lies under to $v$ with $\mathrm{inertiaDeg}'$ equal to $2$ one has $a(v) = 0$ and $\iota(b(v)) = -\psi(\mathfrak{P})$, where $\iota =$ `iotaZsqrtdNegTwo` is the embedding of $\mathbb{Z}[\sqrt{-2}]$ into $\mathbb{C}$ sending $\sqrt{-2}$ to $\sqrt{2}\,i$; assume also that for all $v$ outside some finite set $b(v)$ is the integer $\chi_{-3}(\mathrm{N}v) =$ `chiNegThree` of the absolute norm of $v$, viewed in $\mathbb{Z}[\sqrt{-2}]$. Finally let $0 < c$ and $0 < d_1$. The conclusion asserts the existence of a Hecke eigensystem $\Phi$ over $F$ with coefficients in $\mathbb{Z}[\sqrt{-2}]$ which agrees with $\Phi_0$ in both $a$ and $b$ at all finite places outside some finite set, and of a smooth cusp realisation $R$ for the carrier data `productionPinsOf` whose domain is the union over $x \in T$ of the right translates by $x$ of the centre-cut Siegel set with parameters $c,u,d_1,d_2$, whose level subgroups are the level-one subgroups of the given modulus intersected with the kernel of the archimedean projection, whose Hecke elements are the `heckeGen` $v$ and whose box is `adelicBox` $F$, realising the eigensystem $(\Phi.\mathrm{map}\,\iota).\mathrm{toRawCentral}$, with $a(v) \mapsto \iota(a(v))$ and $b(v) \mapsto (\mathrm{N}v)^{-1}\iota(b(v))$: thus $R$ is a non-zero function on the adelic $\mathrm{GL}_2$ which is a smooth cuspidal automorphic function for a central character on the full central subgroup, invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\iota(a(v))$ and central eigenvalue $(\mathrm{N}v)^{-1}\iota(b(v))$ outside a finite exceptional set. Moreover $R$ satisfies `IsGenuineCuspRealizationAt`, i.e. its underlying function is continuous; at every real infinite place $w$ of $F$ the function satisfies the predicate `HasArchCharacterAt₀` for the weight-one character `archWeightOneAt` at $w$; and it is archimedean-holomorphic at every real place $w$, in the sense that for every $g$ the function $z \mapsto (\mathrm{Im}\,z)^{-1} R(g \cdot \kappa_w(z))$ on the upper half-plane is differentiable, $\kappa_w$ being the Iwasawa section transported to $w$.
--
--   This is the automorphic induction of a narrow ray class character of a quadratic extension $E/F$ that is not Galois-invariant — classically the theta series attached to such a character — packaged as the statement that a Hecke eigensystem recording its traces and determinants at unramified places is realised by a genuine holomorphic weight-one cuspidal function on the adelic $\mathrm{GL}_2$ over $F$, at a level of its own and on a finite union of translated centre-cut Siegel windows. It feeds the Langlands–Tunnell input of the argument, and is used by [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one.lean

import Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
import Definitions.Def_NarrowRayClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel Deep.NTSupply
open NumberField.AdelicLevel NumberField.AdelicBox
open scoped nonZeroDivisors

theorem LanglandsTunnell.exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    {E : Type} [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2)
    (ψ : HeightOneSpectrum (𝓞 E) → ℂˣ) (𝔣 : Ideal (𝓞 E)) (h𝔣 : 𝔣 ≠ ⊥)
    (hψ : ∀ α : 𝓞 E, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) →
      raySymbol E ψ ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1)
    (hcusp : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ v ∉ S, ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 E),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 F) = v ∧ 𝔓₂.under (𝓞 F) = v ∧ ψ 𝔓₁ ≠ ψ 𝔓₂)
    (Φ₀ : HeckeEigensystem F (ℤ√(-2)))
    (hΦ₀ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 E), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 F) = v → 𝔓₂.under (𝓞 F) = v →
        iotaZsqrtdNegTwo (Φ₀.a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧ iotaZsqrtdNegTwo (Φ₀.b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        Φ₀.a v = 0 ∧ iotaZsqrtdNegTwo (Φ₀.b v) = -(ψ 𝔓 : ℂ)))
    (hb : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ₀.b v = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)))
    (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ Φ : HeckeEigensystem F (ℤ√(-2)), Φ.AgreesAwayFromFinite Φ₀ ∧
      (∃ R : SmoothCuspRealizationAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (Φ.map iotaZsqrtdNegTwo).toRawCentral,
        IsGenuineCuspRealizationAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (Φ.map iotaZsqrtdNegTwo).toRawCentral R ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) := by sorry
