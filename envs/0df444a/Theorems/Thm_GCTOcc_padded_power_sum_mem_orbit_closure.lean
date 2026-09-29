-- Prove2me | Theorems.Thm_GCTOcc_padded_power_sum_mem_orbit_closure
-- name    : GCTOcc.padded_power_sum_mem_orbit_closure
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-14T17:34:11.375276+00:00
-- url     : https://prove2.me/theorems/04d2b62a-026b-4a2b-a78f-38ccc213aeb7
-- title:
--   Theorem 2.5 — padded power sums lie in $\Omega_n$
-- statement:
--   Let $X, \varphi_1, \dots, \varphi_k$ be linear forms on $\mathbb{C}^{n\times n}$ and let $s$ be a degree with $sk \le n$. Then the power sum of $k$ terms of degree $s$, padded to degree $n$, lies in the orbit closure of the determinant:
--
--   $$X^{\,n-s}\big(\varphi_1^s + \cdots + \varphi_k^s\big) \;\in\; \Omega_n .$$
--
--   This is the only information about $\Omega_n$ used in the proofs of the two main propositions of the source: $\Omega_n$ contains many padded power sums. The proof combines Valiant's construction — the power sum $X_1^s + \cdots + X_k^s$ can be written with at most $sk - 1$ arithmetic operations and hence has determinantal complexity at most $sk \le n$ — with homogenization and a linear change of coordinates carrying the standard variables to $X, \varphi_1, \dots, \varphi_k$.
--
--   **Formalization note.** Linear forms are given by their coefficient vectors on the $n^2$ matrix positions; $k \ge 1$ is assumed, matching the source's list $\varphi_1, \dots, \varphi_k$, and $sk \le n$ then forces $s \le n$, so the padding exponent $n-s$ is not truncated.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 168, Theorem 2.5.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem padded_power_sum_mem_orbit_closure (n s k : ℕ) (hk : 1 ≤ k) (hsk : s * k ≤ n)
    (a : Fin n × Fin n → ℂ) (phi : Fin k → Fin n × Fin n → ℂ) :
    (linForm n a) ^ (n - s) * (∑ i : Fin k, (linForm n (phi i)) ^ s)
      ∈ orbitClosure n (detPoly n) := by sorry

end GCTOcc
