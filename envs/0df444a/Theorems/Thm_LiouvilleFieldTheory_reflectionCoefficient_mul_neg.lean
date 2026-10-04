-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_reflectionCoefficient_mul_neg
-- name    : LiouvilleFieldTheory.reflectionCoefficient_mul_neg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T10:55:19.033108+00:00
-- url     : https://prove2.me/theorems/aadd88e7-935f-4017-81c7-bb6c89ea73ca
-- title:
--   Reflection relation consistency $R_P\,R_{-P} = 1$
-- statement:
--   Let $b \in \mathbb{C}$ be the coupling constant, $\lambda \in \mathbb{C}\setminus\{0\}$ the normalization parameter, and $P \in \mathbb{C}$ a momentum such that neither $2ibP$ nor $2ib^{-1}P$ is an integer. With the reflection coefficient
--   $$R_P = \pm\,\lambda^{-2iP}\,\frac{\Gamma(2ibP)\,\Gamma(2ib^{-1}P)}{\Gamma(-2ibP)\,\Gamma(-2ib^{-1}P)}$$
--   (sign $+1$ if $c \in (-\infty,1)$, $-1$ otherwise), one has
--   $$R_P\,R_{-P} = 1.$$
--
--   The primary fields $V_P$ and $V_{-P}$ correspond to the same state and are related by the reflection relation $V_P = R_P V_{-P}$; applying it to both $P$ and $-P$ is consistent precisely because $R_P R_{-P} = 1$.
--
--   **Formalization Note** The non-integrality hypothesis keeps all four Gamma factors away from their poles (where Lean's $\Gamma$ returns a junk value); it also forces $b \neq 0$ and $P \neq 0$. $\lambda \neq 0$ is needed because the principal-branch power $0^{w}$ vanishes for $w \neq 0$. This consistency identity is implied by, but not printed in, the source.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Fields and reflection relation (p. 2–3): V_P(z) = R_P V_{−P}(z), formula for R_P.

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem reflectionCoefficient_mul_neg (b lam P : ℂ) (hlam : lam ≠ 0)
    (hP : ∀ n : ℤ, 2 * I * b * P ≠ n ∧ 2 * I * b⁻¹ * P ≠ n) :
    reflectionCoefficient b lam P * reflectionCoefficient b lam (-P) = 1 := by
  sorry

end LiouvilleFieldTheory
