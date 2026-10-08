-- Prove2me | Theorems.Thm_KonyaginUnitVectors_Alon_alon_system
-- name    : KonyaginUnitVectors.Alon.alon_system
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:26:23.253874+00:00
-- url     : https://prove2.me/theorems/692771e5-70d6-49cb-bdfe-7ccc0269a5fc
-- title:
--   Alon's system of unit vectors over GF(2^k)
-- statement:
--   Throughout, $F$ is a finite field of characteristic $2$ with $q$ elements, regarded as an algebra over $\mathbb F_2$ (for example $\mathrm{GF}(2^k)$), $\mathrm{Tr}:F\to\mathbb F_2$ is the absolute trace, and $\psi(y)=(-1)^{\mathrm{Tr}(y)}\in\{1,-1\}$ is the associated additive character of $F$.
--
--   If $q=|F|\ge256$, then there are unit vectors $u_g$, $g\in F^3$, in a Euclidean space such that among any three distinct vectors of the system some two are orthogonal, and
--
--   $$\Bigl\|\sum_{g\in F^3}u_g\Bigr\|\ \ge\ \frac1{13}\,\bigl(q^{3}\bigr)^{2/3}.$$
--
--   With $n=q^3$ vectors the sum thus has norm at least $n^{2/3}/13$. This is the construction behind Alon's lower bound $\Delta_n\ge a\,n^{2/3}$ for orthonormal systems without three pairwise non-orthogonal vectors, which matches Konyagin's upper bound up to the constant.
--
--   **Formalization Note.** The orthogonality condition is stated through the inner product of `EuclideanSpace ℝ (F × F × F)`; the system is indexed by the group $F^3$ itself.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib

namespace KonyaginUnitVectors.Alon

theorem alon_system (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (hq : 256 ≤ Fintype.card F) :
    ∃ u : F × F × F → EuclideanSpace ℝ (F × F × F),
      (∀ g, ‖u g‖ = 1) ∧
      (∀ g h k : F × F × F, g ≠ h → h ≠ k → g ≠ k →
        inner ℝ (u g) (u h) = 0 ∨ inner ℝ (u h) (u k) = 0 ∨ inner ℝ (u g) (u k) = 0) ∧
      (1 / 13 : ℝ) * ((Fintype.card F : ℝ) ^ 3) ^ ((2 : ℝ) / 3) ≤ ‖∑ g, u g‖ := by sorry

end KonyaginUnitVectors.Alon
