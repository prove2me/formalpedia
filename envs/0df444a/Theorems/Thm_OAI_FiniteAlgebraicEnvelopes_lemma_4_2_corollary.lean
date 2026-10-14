-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_2_corollary
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_4_2_corollary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-13T15:06:49.050435+00:00
-- url     : https://prove2.me/theorems/3d2b563f-179c-43f9-89fe-f7404cd135c9
-- title:
--   Corollary of Lemma 4.2: a root word omitting one index with identity matrix is central
-- statement:
--   Let $k \in \{1,\dots,n\}$ and $J = \{1,\dots,n\} \setminus \{k\}$. If $w$ is a root word using only indices in $J$ (i.e. $w \in \mathrm{steinSub}(J)$, so $w$ `omits` the index $k$) and $w$'s matrix image is the identity (i.e. $\pi(w) = I$, where $\pi : \mathrm{St}_n(R) \to \mathrm{GL}_n(R)$ is the Steinberg group's matrix representation), then $w$ is central in $\mathrm{St}_n(R)$: $wv = vw$ for every $v$.
--
--   This is the corollary stated at the end of the preprint's proof of Lemma 4.2 (p. 11): "an element represented by a root word omitting index 6 and having identity matrix is central in $\mathrm{St}_6(R)$" (the preprint fixes $n=6$; this formalization proves the statement for arbitrary $n$ and arbitrary excluded index $k$, specializing to the preprint's case). It is used directly inside the proof of Lemma 4.3.
--
--   **Formalization Note** Proved by the argument the preprint sketches: taking $J$ to be $\{1,\dots,n\}\setminus\{k\}$ in Lemma 4.2's column/row formulas (with $\pi(w)=I$) shows $w$ commutes with every single generator $x_{ik}(a)$ and $x_{ki}(a)$ ($i \ne k$); the remaining generators $x_{ij}(a)$ ($i,j\ne k$) are expressed as the chain-relation commutator $[x_{ik}(a), x_{kj}(1)]$, so $w$ commutes with them too, since commuting with both factors of a commutator implies commuting with the commutator. Since the generators generate $\mathrm{St}_n(R)$ (`PresentedGroup.generated_by`), $w$ is central. Zero `sorry` in the author's own proof, submitted separately as a reduction citing `lemma_4_2`.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone-Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, end of the proof of Lemma 4.2, p. 11.

import Mathlib
import Definitions.Def_BooneHigman_Steinberg

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem lemma_4_2_corollary (k : Fin n) (w : SteinbergGroup n R)
    (J : Finset (Fin n)) (hJ : J = Finset.univ.erase k) (hw : w ∈ steinSub J)
    (hid : steinPi w = 1) (v : SteinbergGroup n R) :
    w * v = v * w := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
