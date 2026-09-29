-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
-- name    : LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/9b42ac17-927f-5f44-b32d-8784fc1a2903
-- title:
--   Inductivity of conductor and root number for a quadratic extension
-- statement:
--   Let $M/E$ be an extension of number fields with $\operatorname{finrank}_E M = 2$, and let $\xi$ be a homomorphism from the ideles of $M$ to $\mathbb{C}^\times$ that is a finite-order Hecke character (trivial on the image of $M^\times$, continuous, of finite order). Assume $\xi$ is unramified outside a finite set $S_0$ of finite places of $M$ (its local character at $w'\notin S_0$ is trivial on units $t$ with $t,t^{-1}$ integral), and that for any two distinct real places $w\neq w'$ of $M$ restricting to the same infinite place of $E$ one has $\xi_w(-1)\,\xi_{w'}(-1)=-1$, the values being taken through the archimedean local characters. Let $\Pi$ be a Hecke eigensystem over $E$ with values in $\mathbb{C}$, i.e. a nonzero level ideal of $\mathcal{O}_E$ together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places of $E$, and let $S$ be a finite set of finite places of $E$ containing every place below a place of $S_0$ and such that every place of $M$ above a place $v\notin S$ has ramification index $1$ over $v$. Assume that for every $v\notin S$: whenever $w'\neq w''$ both lie above $v$, $a_v=\xi(\varpi_{w'})+\xi(\varpi_{w''})$ and $b_v=\xi(\varpi_{w'})\xi(\varpi_{w''})$, where $\varpi_w$ denotes the idele of $M$ that is a uniformizer at $w$ and $1$ elsewhere; and whenever $w'$ lies above $v$ with inertia degree $2$, $a_v=0$ and $b_v=-\xi(\varpi_{w'})$. Then there exist a constant $c\in\mathbb{C}$ and integers $k_v$ for $v\in S$, independent of everything that follows, such that for every continuous unitary idele class character $\mu$ of $E$ that is unramified at each $v\in S$, writing $\lambda=\xi\cdot(\mu\circ N)$ with $N$ the idelic norm attached to the base change $\mathbb{A}_E\to\mathbb{A}_M$ given by `genuineBaseChange E M`, the following hold. First, the conductor $\prod_w q_w^{\,a(\lambda_w)+n(\psi_{M,w})}$ of $\lambda$ equals $\big(\prod_{v\notin S} q_v^{\,2(a(\mu_v)+n(\psi_{E,v}))}\big)\cdot\prod_{v\in S} q_v^{\,k_v}$, where $q$ denotes the absolute norm of the corresponding prime ideal. Second, for all archimedean data $a^{\mathbb{R}}$, $k^{\mathbb{C}}$ over $E$ and $a'^{\mathbb{R}}$, $k'^{\mathbb{C}}$ over $M$ such that $\xi_{w'}(-1)=(-1)^{(a'^{\mathbb{R}}_{w'}-a^{\mathbb{R}}_{w'|_E}).\mathrm{val}}$ at every real place $w'$ of $M$, and $|k'^{\mathbb{C}}_{w'}|$ equals $0$ if $w'|_E$ is real and $|k^{\mathbb{C}}_{w'|_E}|$ otherwise at every complex place $w'$ of $M$, and for all families $u^{\mathbb{R}},u^{\mathbb{C}}$ of complex parameters attached to the real and complex places of $E$, one has $\varepsilon(\lambda)=c\cdot\big(\prod_{v\in S}\mu(\varpi_v)^{k_v}\big)\cdot\varepsilon_{\mathrm{pinned}}$. Here $\varepsilon(\lambda)$ is $\prod_{w'\ \mathrm{real}}\mathrm{signEpsilon}(a'^{\mathbb{R}}_{w'})\cdot\prod_{w'\ \mathrm{complex}} i^{|k'^{\mathbb{C}}_{w'}|}\cdot\prod_{w}\varepsilon(\tfrac12,\lambda_w,\psi_{M,w})$, and $\varepsilon_{\mathrm{pinned}}$ is the pinned root number of $\Pi$, $\mu$ and $S$ over $E$, in which every real place carries the parameter `RealArchParam.oddArtin`, the principal parameter with data $(0,0,0,1)$, every complex place carries `ComplexArchParam.trivialArtin`, the parameter $(0,0,0,0)$, these archimedean parameters are twisted by $u^{\mathbb{R}},a^{\mathbb{R}},u^{\mathbb{C}},k^{\mathbb{C}}$, and the finite part is the product over $v\notin S$ of the good-place root numbers of $\Pi$ and $\mu$.
--
--   This is the global inductivity in degree zero of conductors and $\varepsilon$-factors for the representation of $\mathrm{GL}_2$ over $E$ induced from a Hecke character of a quadratic extension $M/E$, stated in the normalisation pinned to a Hecke eigensystem and with all places of $S$ absorbed into an unknown constant and unknown exponents. It feeds the construction of a nice pinned twisted datum attached to a finite-order Hecke character of a quadratic extension, which is the input to the converse theorem in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.lean

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

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
  LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent

open scoped Classical in

theorem LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
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
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ))) :
    ∃ (c : ℂ) (k : ↥S → ℤ), ∀ (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ), IsAdmissibleTwist E μ →
      (∀ v ∈ S, IsUnramifiedCharAt μ v) →
      heckeConductor M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) =
        finiteConductor E μ S * ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (k v) ∧
      ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          heckeRootNumber M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) aR' kC' =
            c * (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (k v)) *
              pinnedRootNumber E Pi μ S (fun _ _ => RealArchParam.oddArtin)
                (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC := by sorry
