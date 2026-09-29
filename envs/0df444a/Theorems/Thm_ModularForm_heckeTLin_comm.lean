-- Prove2me | Theorems.Thm_ModularForm_heckeTLin_comm
-- name    : ModularForm.heckeTLin_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5111654d-fdf6-5e0f-a74e-66c020b4dca8
-- title:
--   Hecke operators Tₚ, T_q on M_k(Γ₀(N)) commute
-- statement:
--   Let $N$ be a natural number, $k$ an integer, and let $p$ and $q$ be primes, neither dividing $N$ (so in particular $N \neq 0$). Attached to such data is the $\mathbb{C}$-linear endomorphism [`ModularForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L20) of the space `ModularForm (CongruenceSubgroup.Gamma0 N) k` of weight-$k$ modular forms on $\Gamma_0(N)$: it sends $f$ to the function [`ModularForm.heckeT k p ⇑f`](def/ModularForm_HeckeOperator.html#L96), that is to $U_p f + f \mid[k] \, \mathrm{heckeDiagMatrix}\ p$, the sum of the function `heckeU k p ⇑f` and the weight-$k$ slash of $f$ by the diagonal matrix associated with $p$; the hypotheses that $p$ is prime and does not divide $N$ enter as arguments of the operator, being what guarantees that this function is again $\Gamma_0(N)$-invariant of weight $k$, holomorphic and bounded at the cusps. The assertion is that the two endomorphisms [`ModularForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L20) and [`ModularForm.heckeTLin k hq hqN`](def/ModularForm_HeckeOperatorForms.html#L20) commute, i.e. $T_p \circ T_q = T_q \circ T_p$ as $\mathbb{C}$-linear maps on $M_k(\Gamma_0(N))$.
--
--   This is the commutativity of the Hecke operators at primes away from the level on the full space of modular forms (not only on cusp forms), classically part of the statement that the Hecke algebra of $\Gamma_0(N)$ is commutative. It is used in the study of Eisenstein-type eigenvectors and in the passage between mod $p$ eigenforms and eigensystems for the Hecke action on cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeTLin_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (ModularForm.heckeTLin k hp hpN) (ModularForm.heckeTLin k hq hqN) := by sorry
