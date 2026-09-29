-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_adjoin_primes
-- name    : ModularCurve.relfinrank_adjoin_primes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8809b7fa-4e59-5ed7-b88e-84a2475e3da3
-- title:
--   Degree of ℚ(j)(jₚ : p ∈ S) over ℚ(j)
-- statement:
--   Let $S$ be a finite set of natural numbers, every element of which is prime. Work inside the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$ (Hahn series with integer exponents). Here `jq` is the Laurent series $q^{-1}$ (the Hahn series `single (-1) 1`) times the image of the integral power series `jNum` under $\mathbb{Z} \to \mathbb{Q}$, viewed as a Laurent series; and for $N \neq 0$, `jqN N` is the image of `jq` under the ring homomorphism `qExpand`, which multiplies all exponents by $N$, that is, the substitution $q \mapsto q^{N}$. The assertion is that the relative degree, in the sense of `IntermediateField.relfinrank`, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `jq` inside the subfield generated over $\mathbb{Q}$ by `jq` together with all series of the form `jqN p` for $p \in S$ (with $p \neq 0$) equals $\prod_{p \in S} (p+1)$. Since the smaller field is contained in the larger, this is the field degree $[\mathbb{Q}(j, j_p : p \in S) : \mathbb{Q}(j)]$.
--
--   This is the multiplicativity of the degree of the modular equation over squarefree levels: the function field of $X_0(N)$ for $N$ squarefree is generated over $\mathbb{Q}(j)$ by the $j(q^{p})$ for $p \mid N$, of total degree $\prod_{p \mid N}(p+1) = \psi(N)$, equivalently the irreducibility of the modular polynomial $\Phi_N$ over $\mathbb{Q}(j)$ at such levels. It is used, together with [`ModularCurve.full_eq_adjoin_primes`](thm.html#ModularCurve.full_eq_adjoin_primes) and [`ModularCurve.dedekindPsi_of_squarefree`](thm.html#ModularCurve.dedekindPsi_of_squarefree), in the treatment of prime-square levels in [`ModularCurve.relfinrank_full_sq`](thm.html#ModularCurve.relfinrank_full_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_adjoin_primes.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_adjoin_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p})) = ∏ p ∈ S, (p + 1) := by sorry
