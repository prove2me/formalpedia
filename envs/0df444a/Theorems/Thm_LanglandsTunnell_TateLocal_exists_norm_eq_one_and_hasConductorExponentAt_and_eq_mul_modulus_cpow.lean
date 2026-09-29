-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
-- name    : LanglandsTunnell.TateLocal.exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/80839240-a714-5d2c-8ef0-4b8278893557
-- title:
--   Polar decomposition χ = η |·|ᵥ^t of a local quasi-character
-- statement:
--   Let $K$ be a number field, let $v$ be a maximal ideal of the ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and let $\chi \colon (K_v)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the $v$-adic completion $K_v$ to $\mathbb{C}^\times$. Assume $\chi$ has conductor exponent $c \in \mathbb{N}$ in the sense of `HasConductorExponentAt`: $\chi$ is trivial on the set of $u \in (K_v)^\times$ with $\mathrm{v}(u) = 1$ and, when $c \neq 0$, $\mathrm{v}(u - 1) \le \exp(-c)$; and for every $m < c$ there is some $u$ in the corresponding set at level $m$ with $\chi(u) \neq 1$. The conclusion is the existence of a homomorphism $\eta \colon (K_v)^\times \to \mathbb{C}^\times$ and a real number $t$ such that (i) $\lVert \eta(x) \rVert = 1$ for all $x$, (ii) $\eta$ has conductor exponent $c$ in the same sense, and (iii) for every $a \in (K_v)^\times$ one has $\chi(a) = \eta(a) \cdot \mathrm{modulus}(a)^{t}$, the power being the complex power of the real number $\mathrm{modulus}(a)$ with exponent $t$, where $\mathrm{modulus}$ is the scaling factor of the Haar measure of $K_v$ under multiplication (equal to $\lVert a \rVert$ by `modulus_adicCompletion_eq_nnnorm`).
--
--   This is the polar decomposition of a quasi-character of a non-archimedean local field, as in Tate's thesis: every quasi-character is a unitary character times a real power of the normalised absolute value, the unitary factor having the same exact conductor exponent. It is used in the treatment of local zeta integrals, being cited by `exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re`, to reduce statements about general quasi-characters to unitary ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ c) :
    ∃ (η : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ),
      (∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K v η c ∧
      ∀ a : (v.adicCompletion K)ˣ,
        ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (t : ℂ)) := by sorry
