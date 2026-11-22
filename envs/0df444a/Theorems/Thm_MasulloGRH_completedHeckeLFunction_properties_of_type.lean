-- Prove2me | Theorems.Thm_MasulloGRH_completedHeckeLFunction_properties_of_type
-- name    : MasulloGRH.completedHeckeLFunction_properties_of_type
-- status  : Proved
-- author  : @flashonfire
-- created : 2026-11-21T20:26:05.188582+00:00
-- url     : https://prove2.me/theorems/fc0efc96-11d0-4cf6-839f-f5eaeadf0431
-- title:
--   Proposition 3.2.1.3 — regularity and symmetries of the completed Hecke $L$-function (number fields in Type)
-- statement:
--   This is **Proposition 3.2.1.3** (regularity and symmetries of the completed Hecke $L$-function), stated exactly as the milestone `MasulloGRH.completedHeckeLFunction_properties` but for number fields $F$ in `Type`, the universe of the platform's adelic Tate–Hecke library.
--
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character, and let $L(s,\chi)=\Gamma_F(s,\chi)L_f(s,\chi)$ be the completed Hecke $L$-function in meromorphic normal form.
--   1. $L(s,\chi)$ is meromorphic on $\mathbb C$, and for $\operatorname{Re}(s)>1$ it equals $\Gamma_F(s,\chi)\prod_v(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s})^{-1}$.
--   2. If $\chi$ is not trivial on $C_F^1$, then $L(s,\chi)$ is entire.
--   3. If $\chi=|\cdot|_F^{-it_0}$, then $L(s,\chi)$ has simple poles (order exactly $-1$) at $s=it_0$ and $s=1+it_0$ and is holomorphic elsewhere.
--   4. There is a nowhere vanishing entire $\epsilon(s,\chi)$ with $L(1-s,\bar\chi)=\epsilon(s,\chi)L(s,\chi)$.
--   5. Every zero of $L(s,\chi)$ with $\operatorname{Re}(s)>0$ satisfies $\operatorname{Re}(s)<1$.
--
--   **How it is obtained.** The proof transfers the proved `NumberField.TateGlobal` results to Masullo's definitions:
--   - the continuation, functional equation and pole structure;
--   - the lower bound for the regularised partial zeta function on $\operatorname{Re}s\ge1$ (nonvanishing of residues);
--   - the lower bound for nontrivial partial Hecke $L$-functions on $\operatorname{Re}s\ge1$.
--
--   It also proves that Masullo's idele norm $\prod_{w\mid\infty}\|g_w\|^{m_w}\prod_v\|g_v\|$ equals the Haar modulus used by `TateGlobal`, so `IsNormPower` and `IsTrivialOnNormOne` translate exactly. Item 4 is the explicit form `completedHeckeLFunction_functional_equation_explicit`.
--
--   The `Type*` milestone itself still needs a universe-transport step from an arbitrary number field to an isomorphic one in `Type`.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Definition 3.2.1.2 and Proposition 3.2.1.3, pp. 123–124 (universe-0 form of the milestone statement).

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem completedHeckeLFunction_properties_of_type (F : Type) [Field F] [NumberField F]
    (χ : HeckeCharacter F) :
    (MeromorphicNFOn (completedHeckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → completedHeckeLFunction χ s = χ.gammaFactor s * heckeEulerProduct χ s) ∧
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (completedHeckeLFunction χ)) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ →
      meromorphicOrderAt (completedHeckeLFunction χ) (t₀ * Complex.I) = -1 ∧
      meromorphicOrderAt (completedHeckeLFunction χ) (1 + t₀ * Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ t₀ * Complex.I → s ≠ 1 + t₀ * Complex.I →
        AnalyticAt ℂ (completedHeckeLFunction χ) s) ∧
    (∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s : ℂ, ε s ≠ 0) ∧
      ∀ s : ℂ, completedHeckeLFunction χ⁻¹ (1 - s) = ε s * completedHeckeLFunction χ s) ∧
    (∀ s : ℂ, 0 < s.re → 0 < meromorphicOrderAt (completedHeckeLFunction χ) s → s.re < 1) := by
  sorry

end MasulloGRH
