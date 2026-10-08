-- Prove2me | Theorems.Thm_LLLFactor_Factors_prop_2_5
-- name    : LLLFactor.Factors.prop_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:20:21.276337+00:00
-- url     : https://prove2.me/theorems/291f6f45-a39e-49fa-b550-9cde49311d8a
-- title:
--   (2.5) Proposition, p. 526 — f has an irreducible factor h₀ with (h mod p) | (h₀ mod p), unique up to sign; for g | f, (h mod p) | (g mod p) ⇔ (h mod pᵏ) | (g mod pᵏ) ⇔ h₀ | g
-- statement:
--   Let $p$ be a prime, $k\ge1$, $f\in\mathbb Z[X]$ of degree $n>0$, and let $h\in\mathbb Z[X]$ satisfy (2.1)–(2.4): $h$ is monic, $(h\bmod p^k)\mid(f\bmod p^k)$, $(h\bmod p)$ is irreducible in $\mathbb F_p[X]$, and $(h\bmod p)^2\nmid(f\bmod p)$.
--
--   Then:
--
--   1. $f$ has an irreducible factor $h_0$ in $\mathbb Z[X]$ for which $(h\bmod p)$ divides $(h_0\bmod p)$;
--   2. this factor is uniquely determined up to sign: any two such factors $h_0,h_0'$ satisfy $h_0'=\pm h_0$;
--   3. for every such $h_0$ and every $g\in\mathbb Z[X]$ dividing $f$, the following are equivalent:
--   $$\text{(i) } (h\bmod p)\mid(g\bmod p)\ \text{in }\mathbb F_p[X],\qquad \text{(ii) } (h\bmod p^k)\mid(g\bmod p^k)\ \text{in }(\mathbb Z/p^k\mathbb Z)[X],\qquad \text{(iii) } h_0\mid g\ \text{in }\mathbb Z[X];$$
--   4. in particular $(h\bmod p^k)$ divides $(h_0\bmod p^k)$.
--
--   The proposition identifies the integer factor of $f$ that the $p$-adic factor $h$ singles out, and translates divisibility by $h_0$ into a congruence condition modulo $p^k$; that is what makes $h_0$ an element of the lattice $L$ of (2.6).
--
--   **Formalization Note** The equivalence of (i), (ii), (iii) is stated as (i) ⇔ (ii) and (ii) ⇔ (iii). The standing assumptions are bundled in `IsSetting p k f h`.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 526, (2.5) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem prop_2_5 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h) :
    (∃ h₀ : ℤ[X], IsH0 p f h h₀) ∧
    (∀ h₀ h₀' : ℤ[X], IsH0 p f h h₀ → IsH0 p f h h₀' → h₀' = h₀ ∨ h₀' = -h₀) ∧
    (∀ h₀ : ℤ[X], IsH0 p f h h₀ → ∀ g : ℤ[X], g ∣ f →
      ((modPk p h ∣ modPk p g ↔ modPk (p ^ k) h ∣ modPk (p ^ k) g) ∧
       (modPk (p ^ k) h ∣ modPk (p ^ k) g ↔ h₀ ∣ g))) ∧
    (∀ h₀ : ℤ[X], IsH0 p f h h₀ → modPk (p ^ k) h ∣ modPk (p ^ k) h₀) := by sorry

end LLLFactor.Factors
