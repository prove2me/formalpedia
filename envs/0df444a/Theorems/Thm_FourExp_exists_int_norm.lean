-- Prove2me | Theorems.Thm_FourExp_exists_int_norm
-- name    : FourExp.exists_int_norm
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:44:07.770429+00:00
-- url     : https://prove2.me/theorems/3b96e024-7747-4dc5-92bd-7e2392eba335
-- title:
--   Norms from a finite extension of ℚ(ω) to ℚ(ω), with size control
-- statement:
--   Let $Q \in \mathbb{Z}[X][Y]$ be monic in $Y$ of degree $d$, vanishing at $(\omega, \omega_1)$ and minimal there: no non-zero polynomial of $Y$-degree less than $d$ vanishes at $(\omega, \omega_1)$. There is $c$ such that for every $\mathrm{Pol} \in \mathbb{Z}[X][Y]$ of $Y$-degree less than $d$, length at most $b$ and $X$-degree at most $e$, with $\mathrm{Pol}(\omega, \omega_1) \neq 0$, there is $P \in \mathbb{Z}[X]$, $P \neq 0$, with length at most $(cb)^{d}$, degree at most $d(e + c)$, and
--
--   $$|P(\omega)| \le |\mathrm{Pol}(\omega, \omega_1)|\,\big(c\,b\,\max(1, |\omega|)^{e}\big)^{d}.$$
--
--   $P$ is the determinant of multiplication by $\mathrm{Pol}$ on $\mathbb{Z}[X][Y]/(Q)$ in the basis $1, Y, \dots, Y^{d-1}$: the norm from $\mathbb{Q}(\omega, \omega_1)$ to $\mathbb{Q}(\omega)$, up to the denominators. No hypothesis on $\omega$ is needed.
-- source:
--   The core of the proof of Lemma 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

theorem exists_int_norm (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) :
    ∃ c : ℕ, ∀ (Pol : Polynomial (Polynomial ℤ)) (b e : ℕ), Pol.natDegree < Q.natDegree →
      ∑ k ∈ Pol.support, ∑ i ∈ (Pol.coeff k).support, ((Pol.coeff k).coeff i).natAbs ≤ b →
      (∀ k, (Pol.coeff k).natDegree ≤ e) →
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Pol ≠ 0 →
      ∃ P : Polynomial ℤ, P ≠ 0 ∧
        ∑ i ∈ P.support, (P.coeff i).natAbs ≤ (c * b) ^ Q.natDegree ∧
        P.natDegree ≤ Q.natDegree * (e + c) ∧
        ‖Polynomial.aeval ω P‖ ≤
          ‖Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Pol‖ *
            (((c * b : ℕ) : ℝ) * max 1 ‖ω‖ ^ e) ^ Q.natDegree := by
  sorry

end FourExp
