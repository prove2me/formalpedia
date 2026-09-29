-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- name    : LanglandsTunnell.exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/e7e22e4b-fcb6-5d32-8f22-ffc9ce534c42
-- title:
--   Induced datum from a finite-order Hecke character is nicely pinned
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra of degree $\mathrm{finrank}_E M = 2$, and let $\xi$ be a homomorphism from the ideles $(\mathbb{A}_M)^\times$ to $\mathbb{C}^\times$ which is a finite-order Hecke character, i.e. trivial on the image of $M^\times$, continuous and of finite order. Let $S_0$ be a finite set of primes of $\mathcal{O}_M$ such that for every $w'\notin S_0$ the local character of $\xi$ at $w'$ is trivial on the units of the local ring; assume that any two distinct real places $w\neq w'$ of $M$ with the same restriction to $E$ satisfy $\xi_w(-1)\,\xi_{w'}(-1)=-1$, and that there are distinct primes $w',w''\notin S_0$ lying under the same prime of $\mathcal{O}_E$ with $\xi(\varpi_{w'})\neq\xi(\varpi_{w''})$, where $\varpi_w$ denotes the uniformizer idele at $w$. Then for every finite set $T_0$ of primes of $\mathcal{O}_E$ there exist a Hecke eigensystem $\Pi$ over $E$ with complex coefficients (a nonzero level ideal together with functions $a,b$ on the primes of $\mathcal{O}_E$), a finite set $S\supseteq T_0$ of primes of $\mathcal{O}_E$, and functions $A,A^\vee\colon(S\to\mathbb{Z})\to\mathbb{C}$ with the following properties. For $w\notin S$: whenever $w'\neq w''$ are primes of $\mathcal{O}_M$ lying under $w$ one has $\Pi.a\,w=\xi(\varpi_{w'})+\xi(\varpi_{w''})$ and $\Pi.b\,w=\xi(\varpi_{w'})\xi(\varpi_{w''})$, and whenever $w'$ lies under $w$ with inertia degree $2$ one has $\Pi.a\,w=0$ and $\Pi.b\,w=-\xi(\varpi_{w'})$. The families $A$ and $A^\vee$ are bounded by a single constant, there is $n_0$ with $A n=A^\vee n=0$ as soon as $n_v<n_0(v)$ for some $v$, and $A\neq0$. Finally, for every character $\mu\colon(\mathbb{A}_E)^\times\to\mathbb{C}^\times$ that is trivial on $E^\times$, continuous and unitary, whose local character at each $v\in S$ is trivial on the units of valuation $1$, and for all archimedean data $u_R,a_R\in\mathbb{Z}/2,u_C,k_C$ describing $\mu$ at the real places by $x\mapsto\|x\|^{\,\mathrm{mult}\cdot u_R}(x/\|x\|)^{a_R}$ and at the complex places by the corresponding formula with exponent $k_C$, the $L$-datum obtained by twisting $\Pi$ by $\mu$ outside $S$ — Euler factors $1-\mu(\varpi_v)\Pi.a\,v\,X+\mu(\varpi_v)^2\Pi.b\,v\,X^2$ at places where $\mu$ is unramified and $1$ elsewhere, with their duals, gamma factors the twists of the odd Artin parameter $\mathrm{principal}\,0\,0\,0\,1$ at real places and of the trivial parameter at complex places, abscissa $1$, centre $1/2$, degree $2$ — is nicely pinned with $S$-parts $\sum_n A n\prod_{v\in S}(\mu(\varpi_v)\,\mathrm{N}v^{1/2-s})^{n_v}$ and its dual analogue, root number the product of the archimedean epsilon factors with the Euler root numbers outside $S$, and conductor $\prod_{v\notin S}\mathrm{N}v^{2\,\mathrm{pinnedExp}}$: that is, the datum is well formed and convergent, the conductor is positive, and the products of the $S$-parts with the archimedean factor and the $L$-function, respectively their duals, agree on $\mathrm{Re}\,s>1$ with entire functions bounded on vertical strips linked by the functional equation with that root number and conductor.
--
--   This is the analytic input needed to run the $\mathrm{GL}(2)$ converse theorem for the two-dimensional datum induced from a finite-order Hecke character of a quadratic extension, in the form used in Jacquet–Langlands' treatment of automorphic induction: the twisted completed $L$-functions in play are Hecke's $\Lambda(s,\xi\cdot(\mu\circ\mathrm{N}_{M/E}))$, regrouped into an Euler product over the primes of $E$. It is used to produce a cuspidal Hecke eigensystem over $E$ with prescribed archimedean weight whose Hecke data off a finite set match the induced representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
  LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (T₀ : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E))) (A Ad : (↥S → ℤ) → ℂ),
      T₀ ⊆ S ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
        (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
          Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
          Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
        (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
          Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ))) ∧
      (∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
      (∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
      A ≠ 0 ∧
      (∀ μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsAdmissibleTwist E μ →
        (∀ v ∈ S, ∀ t : (v.adicCompletion E)ˣ, Valued.v (t : v.adicCompletion E) = 1 →
          localChar μ v t = 1) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ)
          (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ)
          (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw)) →
          IsNicePinned
            (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
              (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC)
            (sPart E S A μ) (sPartDual E S Ad μ)
            (pinnedRootNumber E Pi μ S (fun _ _ => RealArchParam.oddArtin)
              (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC)
            (finiteConductor E μ S)) := by sorry
