-- Prove2me | Theorems.Thm_GCTOcc_no_occurrence_obstructions
-- name    : GCTOcc.no_occurrence_obstructions
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T18:08:26.20227+00:00
-- url     : https://prove2.me/theorems/a586c963-1471-4731-99f3-ae24f6bd6f95
-- title:
--   Theorem 1.4 (Main Theorem) — no occurrence obstructions in geometric complexity theory
-- statement:
--   Let $n, d, m$ be positive integers with $n \ge m^{25}$, and let $\lambda \vdash nd$ be a partition with at most $n^2$ parts. If $\lambda$ occurs in the degree $d$ part of the coordinate ring of the orbit closure $Z_{n,m}$ of the padded permanent, then $\lambda$ also occurs in the degree $d$ part of the coordinate ring of the orbit closure $\Omega_n$ of the determinant:
--
--   $$\lambda \text{ occurs in } \mathbb{C}[Z_{n,m}]_d \;\Longrightarrow\; \lambda \text{ occurs in } \mathbb{C}[\Omega_n]_d .$$
--
--   Equivalently: **there are no occurrence obstructions** once the padding is at least $m^{25}$. Since the existence of such obstructions for $n = m^c$ and infinitely many $m$ was the conjecture of Mulmuley and Sohoni (Conjecture 1.3 of the source) on which the representation-theoretic approach to the permanent versus determinant problem rested, that conjecture is false, and lower bounds on determinantal complexity cannot be obtained by exhibiting a partition that occurs on one side and not on the other. The statement leaves open the multiplicity-based variant, where one compares the multiplicity of $\lambda$ on the two sides rather than mere occurrence, and it leaves Valiant's conjecture itself untouched.
--
--   **Formalization note.** Occurrence is the existence of a degree $d$ Borel eigenvector of weight $\lambda$ on the space of degree $n$ forms which is nonzero somewhere on the set in question; the exponent $25$ is the one proved in the source, which notes that it can likely be improved.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 165, Theorem 1.4 (Main Theorem); the notions of occurrence and of occurrence obstruction are on pp. 164–165, and Conjecture 1.3 (refuted by this theorem) is on p. 165.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem no_occurrence_obstructions (n d m : ℕ) (hn : 0 < n) (hd : 0 < d) (hm : 0 < m)
    (hnm : m ^ 25 ≤ n) (lam : ℕ → ℕ) (hlam : IsPartitionOf lam (n * n) (n * d))
    (h : Occurs n d lam (orbitClosure n (paddedPerm m n))) :
    Occurs n d lam (orbitClosure n (detPoly n)) := by sorry

end GCTOcc
