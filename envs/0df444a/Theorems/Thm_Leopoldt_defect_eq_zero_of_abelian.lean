-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_zero_of_abelian
-- name    : Leopoldt.defect_eq_zero_of_abelian
-- status  : Proved
-- author  : @kbuzzard
-- created : 2026-09-09T09:32:45.486812+00:00
-- url     : https://prove2.me/theorems/50e8389c-a535-4e83-9d3a-9c719d73d99e
-- title:
--   Brumer's theorem: Leopoldt's conjecture for abelian extensions of $\mathbb{Q}$
-- statement:
--   This is Brumer's theorem, the established abelian case of Leopoldt's conjecture, recorded in the introduction of the source as the starting point of the subject.
--
--   Let $p$ be a prime and let $\mathbb{K}$ be a number field which is a Galois extension of $\mathbb{Q}$ with abelian Galois group $\mathrm{Gal}(\mathbb{K}/\mathbb{Q})$. Then the Leopoldt defect of $\mathbb{K}$ at $p$ vanishes:
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; 0 .$$
--
--   No hypothesis is placed on $p$ beyond primality, and $\mathbb{K}$ is not assumed CM or totally real.
--
--   The result is due to Brumer (1967), following a reduction of Ax and using Baker's theorem on linear forms in logarithms adapted to the $p$-adic topology. It is the only case of the conjecture that is unconditionally established for an infinite family of fields with arbitrary unit rank, and it is the benchmark any new approach must recover. Within this mission it also serves as a consistency check on the definitions: a formalization of the defect under which Brumer's theorem failed would be misdefined.
--
--   **Formalization Note** "Abelian extension of $\mathbb{Q}$" is expressed as the conjunction of $\mathbb{K}$ being Galois over $\mathbb{Q}$ and the group of $\mathbb{Q}$-algebra automorphisms of $\mathbb{K}$ being commutative.
-- source:
--   Attribution as given in Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1 (Introduction), p. 2 ('It was proved for the abelian case in 1967 by Brumer, using Baker theory' / 'This fact could be proved by Brumer in 1967, using a plan of Ax, as soon as Baker had proved his archimedean version'). Original: A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124, https://doi.org/10.1112/S0025579300003703; reduction in J. Ax, On the units of an algebraic number field, Illinois J. Math. 9 (1965), 584-589.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_zero_of_abelian (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [IsMulCommutative (K ≃ₐ[ℚ] K)] :
    defect p K = 0 := by sorry
end Leopoldt
