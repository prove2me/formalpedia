-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_3
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_4_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-13T15:54:33.052698+00:00
-- url     : https://prove2.me/theorems/a0899827-aeb3-41c4-9948-79f68b3ea56e
-- title:
--   Lemma 4.3 (central elements from corner data)
-- statement:
--   Let $E, F \in R$ be idempotents with $EF = FE = 0$, and suppose $d, d^* \in R$ satisfy $d = FdE$, $d^* = Ed^*F$, $d^*d = E$, $dd^* = F$. Let $p \ne q$ be indices for which a third index $k_0 \notin \{p,q\}$ exists (automatic whenever $n \ge 3$). If $w_0 \in \mathrm{cornerSub}(E)$ -- a root word whose coefficients lie in the corner $ERE$ -- has identity matrix ($\pi(w_0) = I$), then $w_0$ is central in $\mathrm{St}_n(R)$: $w_0 v = v w_0$ for every $v$.
--
--   This is the preprint's Lemma 4.3. Its proof constructs the auxiliary element $W = x_{pq}(d)\,x_{qp}(-d^*)\,x_{pq}(d)$, whose matrix on the pair $(p,q)$ is $H = \begin{pmatrix} 1-F & d \\ -d^* & 1-E \end{pmatrix}$ (equation (18)); conjugating any root word with coefficients in $ERE$ by $W$ moves every generator to one omitting the index $q$, while preserving the identity matrix, so Lemma 4.2's corollary makes $W w_0 W^{-1}$ central; conjugation by $W$ is injective, so $w_0$ itself is central.
--
--   **Formalization Note** The preprint fixes $n = 6$ and the pair $(1,6)$; this formalization proves the statement for an arbitrary ring size $n$ and arbitrary distinct pair $(p,q)$ admitting a third index, specializing to the preprint's case. The existence hypothesis `hex` replaces the preprint's implicit use of $n = 6 \ge 3$. Zero `sorry` in the author's own proof, submitted separately, which cites the already-published `lemma_4_2` and `lemma_4_2_corollary` as reductions.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone-Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Lemma 4.3, p. 11.

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_BooneHigman_cornerSub

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem lemma_4_3 (E F d dstar : R) {p q : Fin n} (hpq : p ≠ q)
    (hex : ∃ k0 : Fin n, k0 ≠ p ∧ k0 ≠ q)
    (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0) (hF : F * F = F)
    (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (w0 : SteinbergGroup n R) (hw0 : w0 ∈ cornerSub E) (hid : steinPi w0 = 1)
    (v : SteinbergGroup n R) :
    w0 * v = v * w0 := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
