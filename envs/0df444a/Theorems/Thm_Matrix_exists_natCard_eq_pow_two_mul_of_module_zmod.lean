-- Prove2me | Theorems.Thm_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod
-- name    : Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/6f76db6b-f912-52f8-a7ea-033b53afaf6d
-- title:
--   Finite M₂(𝔽_ℓ)-modules have order ℓ^{2k}
-- statement:
--   Let $\ell$ be a natural number carrying the hypothesis that it is prime, and let $V$ be a type equipped with an additive commutative group structure together with a module structure over the ring $\mathrm{Matrix}\,(\mathrm{Fin}\,2)\,(\mathrm{Fin}\,2)\,(\mathbb{Z}/\ell)$ of $2\times 2$ matrices over $\mathbb{Z}/\ell \cong \mathbb{F}_\ell$, and assume $V$ is finite. The conclusion asserts the existence of a natural number $k$ with $\operatorname{card} V = \ell^{2k}$, where $\operatorname{card}$ is the cardinality of $V$ as a natural number. Thus the order of a finite module over $M_2(\mathbb{F}_\ell)$ is an even power of $\ell$; in particular it is a power of $\ell$, and $V$ cannot have order $\ell$, $\ell^3$, or any order divisible by a prime other than $\ell$. No faithfulness, unitality beyond the module axioms, or finite generation hypothesis is imposed beyond finiteness of $V$ itself; the case $V$ trivial is covered by $k = 0$.
--
--   This is the finite-group form of the Morita equivalence between $M_2(\mathbb{F}_\ell)$-modules and $\mathbb{F}_\ell$-vector spaces: a module over the matrix ring splits as $eV \oplus (1-e)V$ for $e = E_{11}$, the two summands being exchanged by $E_{12}+E_{21}$, so its $\mathbb{F}_\ell$-dimension is even. It is used in the Čerednik–Drinfeld part of the development to constrain the possible orders of $\Lambda$-stable subgroups of the $\ell$-torsion of a fake elliptic curve, where $\Lambda/\ell\Lambda \cong M_2(\mathbb{F}_\ell)$ acts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
    ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by sorry
