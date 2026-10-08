-- Prove2me | Theorems.Thm_LLLFactor_Factors_claim_2_11
-- name    : LLLFactor.Factors.claim_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:20:35.852122+00:00
-- url     : https://prove2.me/theorems/a338a6e1-de7d-4053-bba8-51e20353e5fc
-- title:
--   (2.11), proof of (2.7), p. 527 — if (h mod p) ∤ (gcd(f,b) mod p), every v ∈ M with deg v < e + l lies in pᵏℤ[X]
-- statement:
--   Assume the setting of Sect. 2: $p$ prime, $k\ge1$, $f\in\mathbb Z[X]$ of degree $n>0$, $h$ satisfying (2.1)–(2.4), $l=\deg h$, and an integer $m\ge l$. Let $b\neq0$ be an element of the lattice $L$ of (2.6), and let $g$ be a greatest common divisor of $f$ and $b$ in $\mathbb Z[X]$ (a common divisor that every common divisor divides). Suppose that $(h\bmod p)$ does **not** divide $(g\bmod p)$ in $\mathbb F_p[X]$. Put $e=\deg g$, $m'=\deg b$ and
--   $$M=\{\lambda f+\mu b:\ \lambda,\mu\in\mathbb Z[X],\ \deg\lambda<m'-e,\ \deg\mu<n-e\}.$$
--   Then
--   $$\{v\in M:\ \deg v<e+l\}\subset p^k\mathbb Z[X],$$
--   that is, every coefficient of such a $v$ is divisible by $p^k$.
--
--   This is the key step in the proof by contradiction of Proposition (2.7): combined with a determinant bound it shows that the assumption $(h\bmod p)\nmid(g\bmod p)$ is impossible.
--
--   **Formalization Note** Degrees of $\lambda,\mu,v$ are Mathlib's `degree` with values in `WithBot ℕ`, so $\lambda=0$ or $\mu=0$ (degree $-\infty$) is allowed, as on the page. The differences $m'-e$ and $n-e$ are natural-number differences; they are exact because $g$ divides the nonzero polynomials $b$ and $f$. The page derives (2.11) from the Bézout relation (2.9), which itself follows from $(h\bmod p)\nmid(g\bmod p)$ and (2.3); the Lean statement assumes the non-divisibility, not (2.9).
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 527, (2.11) in the proof of (2.7) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem claim_2_11 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m)
    (b : ℤ[X]) (hbL : b ∈ latticeL p k h m) (hb0 : b ≠ 0)
    (g : ℤ[X]) (hgf : g ∣ f) (hgb : g ∣ b) (hg_gcd : ∀ d : ℤ[X], d ∣ f → d ∣ b → d ∣ g)
    (hndvd : ¬ modPk p h ∣ modPk p g) :
    ∀ lam mu' : ℤ[X],
      lam.degree < ((b.natDegree - g.natDegree : ℕ) : WithBot ℕ) →
      mu'.degree < ((f.natDegree - g.natDegree : ℕ) : WithBot ℕ) →
      (lam * f + mu' * b).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) →
      ∀ i : ℕ, ((p ^ k : ℕ) : ℤ) ∣ (lam * f + mu' * b).coeff i := by sorry

end LLLFactor.Factors
