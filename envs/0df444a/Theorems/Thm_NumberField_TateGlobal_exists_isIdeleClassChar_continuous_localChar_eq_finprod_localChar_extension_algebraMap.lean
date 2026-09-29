-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
-- name    : NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/40e91290-4944-5888-a73e-7142024138a0
-- title:
--   Restriction of an idele class character to a subfield
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra, and let $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a monoid homomorphism on the units of the adele ring of $K$ which is an idele class character, i.e. $\mu$ kills every principal idele $\mathrm{algebraMap}(u)$ with $u \in K^\times$, and which is continuous. Then there exists a monoid homomorphism $\nu\colon (\mathbb{A}_E)^\times \to \mathbb{C}^\times$ which is again trivial on the image of $E^\times$ and continuous, and whose local components are compatible with those of $\mu$ in the following sense: for every height-one prime $v$ of $\mathcal{O}_E$ and every unit $x$ of the completion $E_v$, the value of `localChar ν v` at $x$ — that is, $\nu$ evaluated at the idele whose $v$-component is $x$, whose other finite components are $1$ and whose infinite component is $1$ — equals, as a complex number, the finitely supported product $\prod^{f}_{w}$ over the subtype of height-one primes $w$ of $\mathcal{O}_K$ lying under $v$ of the values of `localChar μ w` at the image of $x$ under the induced map of units $(E_v)^\times \to (K_w)^\times$ coming from the canonical algebra map $E_v \to K_w$.
--
--   This is the restriction of a Hecke (idele class) character of $K$ to the subfield $E$ along the base-change map $(\mathbb{A}_E)^\times \to (\mathbb{A}_K)^\times$, packaged together with the resulting local formula $\nu_v = \prod_{w \mid v} \mu_w \circ i_w$ at each finite place. It is used in the cubic-induction part of the Langlands–Tunnell argument, where central characters and conductor exponents of an induced representation are compared with those of the inducing character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm

theorem NumberField.TateGlobal.exists_isIdeleClassChar_continuous_localChar_eq_finprod_localChar_extension_algebraMap
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcont : Continuous μ) :
    ∃ ν : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 E) E ν ∧ Continuous ν ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ),
        ((localChar ν v x : ℂˣ) : ℂ) =
          ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ) := by sorry
