-- Prove2me | Theorems.Thm_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
-- name    : LanglandsTunnell.wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3580ece7-ad47-5ee4-9d26-613360fdec37
-- title:
--   Artin induction of L- and Γ-factors in a quadratic extension
-- statement:
--   Let $E \subset M$ be number fields with $[M:E]=2$, and let $\xi$ be a character of the idele group of $M$ which is trivial on $M^\times$, continuous and of finite order, unramified (its local character trivial on the local units) outside a finite set $S_0$ of finite places of $M$, and such that for any two distinct real places $w \neq w'$ of $M$ with the same restriction to $E$ the product of the archimedean local characters of $\xi$ at $-1$ equals $-1$. Let $\Pi$ be a Hecke eigensystem over $E$ with values in $\mathbb{C}$ (a nonzero level ideal together with coefficient functions $a, b$ on finite places), and let $S$ be a finite set of finite places of $E$ containing all places under $S_0$ and such that every place of $M$ above a place $v \notin S$ has ramification index $1$; assume that for $v \notin S$ the coefficients match the induced data: if two distinct places $w', w''$ of $M$ lie over $v$ then $a_v = \xi(\varpi_{w'}) + \xi(\varpi_{w''})$ and $b_v = \xi(\varpi_{w'})\xi(\varpi_{w''})$, and if a place $w'$ over $v$ has inertia degree $2$ then $a_v = 0$ and $b_v = -\xi(\varpi_{w'})$, where $\varpi$ denotes the uniformizer idele. Let $\mu$ be a continuous unitary character of the idele group of $E$ trivial on $E^\times$, with archimedean data $(u_w, a_w) \in \mathbb{C} \times \mathbb{Z}/2$ at the real places and $(u_w, k_w) \in \mathbb{C} \times \mathbb{Z}$ at the complex places, in the sense that the local character of $\mu$ at $w$ sends $x$ to $\|x\|^{\operatorname{mult}(w) u_w}\,(x/\|x\|)^{a_w}$, respectively $(x/\|x\|)^{k_w}$, under the embedding of the completion. Let archimedean data $(u'_{w'}, a'_{w'})$, $(u'_{w'}, k'_{w'})$ over $M$ be given, subject to: at a real place $w'$ of $M$, $u'_{w'} = u_{w}$ for $w$ the place below and the archimedean local character of $\xi$ at $-1$ equals $(-1)^{(a'_{w'} - a_{w}).\mathrm{val}}$; at a complex place $w'$ of $M$, $u'_{w'}$ is $u_w$ for $w$ the place below (real or complex) and $|k'_{w'}|$ is $0$ if $w$ is real and $|k_w|$ if $w$ is complex. Write $D$ for the degree-two $L$-datum `twistedDatum` attached to $E$, $\Pi$, $S$, $\mu$ and the archimedean data over $E$, in which the real parameter at every real place is obtained by twisting $\mathrm{principal}\,(0,0,0,1)$ by $(u_w, a_w)$ and the complex parameter at every complex place by twisting $(0,0,0,0)$ by $(u_w, k_w)$; its index set is the set of finite places $v \notin S$, its Euler factor there is $1 - \mu(\varpi_v)a_v X + \mu(\varpi_v)^2 b_v X^2$ when $\mu$ is unramified at $v$ and $1$ otherwise, with dual factor $1 - \mu(\varpi_v)^{-1}(a_v/b_v)X + \mu(\varpi_v)^{-2}b_v^{-1}X^2$, abscissa $1$, centre $1/2$ and degree $2$. Write $D'$ for the degree-one $L$-datum `heckeDatum` of the character $\lambda = \xi \cdot (\mu \circ N)$ of $M$, $N$ being the idelic norm of the genuine adelic base change of $M/E$, with the archimedean data $(u', a', k')$ over $M$. Then: $D$ is well formed (all norms are at least $2$, all Euler and dual polynomials have constant term $1$ and degree at most $2$, and every gamma parameter $\nu$ satisfies $-\operatorname{Re}\nu \le 1$); $D$ converges (for $\operatorname{Re} s > 1$ the series of norms of the Euler and dual factors minus $1$ are summable and the two Euler products are nonzero); for every $s$ the archimedean factor and the dual archimedean factor of $D'$ coincide with those of $D$; and for every $s$ with $\operatorname{Re} s > 1$ the $L$-function of $D'$ equals the product over all finite places $w'$ of $M$ lying over $S$ of the inverted local Euler factors of $D'$ at $(\#\mathcal{O}/w')^{-s}$, times the $L$-function of $D$, and likewise for the dual $L$-functions with the dual polynomials.
--
--   This is Artin's formalism of invariance of $L$-functions under induction, carried out place by place for the two-dimensional datum over $E$ induced from a finite-order Hecke character $\xi$ of a quadratic extension $M$ and twisted by an idele class character $\mu$: the degree-one datum of $\xi \cdot (\mu \circ N)$ over $M$ and the degree-two twisted datum over $E$ have the same archimedean factors and the same $L$-functions up to the explicitly isolated factors at places above $S$. It supplies the analytic input for producing a nicely pinned $L$-datum from such a Hecke character, the step feeding the converse theorem in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Polynomial
  LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent

open scoped Classical in

theorem LanglandsTunnell.wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw))
    (uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (huR' : ∀ w', ∀ hw' : w'.IsReal,
      uR' w' hw' = uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val)
    (huC' : ∀ w', ∀ hw' : w'.IsComplex,
      uC' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then uR _ h
        else uC _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) :
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).WellFormed ∧
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).Converges ∧
    (∀ s : ℂ,
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactor s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactor s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactorDual s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactorDual s) ∧
    (∀ s : ℂ, 1 < s.re →
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFun s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').euler w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFun s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFunDual s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').dual w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFunDual s) := by sorry
