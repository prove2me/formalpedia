-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
-- name    : LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d0f946a2-dbbc-55fe-ab6b-40136f9c2f11
-- title:
--   Localisation of a twisted unit integral on the critical shell
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $\mathcal O_K$, and $F = K_v$ the $v$-adic completion, carried with a Borel measurable structure and an additive Haar measure $\mu$. Let $\psi : F \to \mathbb C$ be an additive character and $n \in \mathbb Z$ such that $\psi(x) = 1$ whenever $v(x) \le \exp(n)$, while some $x$ with $v(x) \le \exp(n+1)$ has $\psi(x) \neq 1$. Let $\chi : F^\times \to \mathbb C^\times$ be a homomorphism, and let $a, h \in \mathbb N$ with $1 \le h$ and $a \le 2h$; assume $\chi(u) = 1$ for every unit $u$ in `higherUnitsAt K v a`, i.e. every unit with $v(u) = 1$ and (if $a \neq 0$) $v(u - 1) \le \exp(-a)$. Assume further that $\chi$ is linearised on `higherUnitsAt K v h` by an element $c \in F$: $\chi(u) = \psi(c\,(u-1))$ for all such $u$. Let $z \in F$ satisfy $v(z) = \exp(n+a)$, and let $f : F \to \mathbb C$ satisfy $f(u w) = f(u)$ for every unit $u$ with $v(u) = 1$ and every $w$ in `higherUnitsAt K v (a - h)`, the truncated difference being meant. Write $\mathrm{charExt}\,\chi$ for the extension of $\chi$ to $F$ by $0$ at $0$, and let all integrals be over $\{u : v(u) = 1\}$ against $\mu$. Then two statements hold simultaneously: (1) for every $u_1 \in F$ with $v(u_1) = 1$ and $v(z u_1 + c) \le \exp(n+h)$, one has $\int \psi(zu) f(u)\,\mathrm{charExt}\,\chi(u) = f(u_1) \int \psi(zu)\,\mathrm{charExt}\,\chi(u)$; and (2) if $v(z u + c) > \exp(n+h)$ for every $u$ with $v(u) = 1$, then $\int \psi(zu) f(u)\,\mathrm{charExt}\,\chi(u) = 0$.
--
--   This is the test-function form of Deligne's lemma on characters of large level: on the critical shell $v(z) = \exp(n+a)$ the twisted Gauss integral over the unit circle is supported on the single coset of units solving $z u + c \equiv 0$ to precision $\exp(n+h)$, so that any function invariant under the higher units $1 + \mathfrak p^{a-h}$ may be replaced by its constant value there, and the integral vanishes when no such unit exists. It is used in the computation of local root numbers for Whittaker models, being cited in the evaluation of the dual of a torus shell at the relevant place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem
  LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a h : ℕ) (hh : 1 ≤ h) (hah : a ≤ 2 * h)
    (hχa : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
    (c : v.adicCompletion K)
    (hc : ∀ u ∈ higherUnitsAt K v h, ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : v.adicCompletion K) - 1)))
    (z : v.adicCompletion K) (hz : Valued.v z = WithZero.exp (n + a))
    (f : v.adicCompletion K → ℂ)
    (hf : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v (a - h), f ((u : v.adicCompletion K) * w) = f u) :
    (∀ u₁ : v.adicCompletion K, Valued.v u₁ = 1 → Valued.v (z * u₁ + c) ≤ WithZero.exp (n + h) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) =
        f u₁ * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * charExt χ u ∂μ) ∧
    ((∀ u : v.adicCompletion K, Valued.v u = 1 → WithZero.exp (n + h) < Valued.v (z * u + c)) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) = 0) := by sorry
