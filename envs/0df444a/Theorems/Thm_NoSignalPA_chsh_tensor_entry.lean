-- Prove2me | Theorems.Thm_NoSignalPA_chsh_tensor_entry
-- name    : NoSignalPA.chsh_tensor_entry
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:04:29.129276+00:00
-- url     : https://prove2.me/theorems/484f958f-d2ec-4610-bf82-72ba0a5c67e3
-- title:
--   Entries of $|\mathrm{CHSH}\rangle^{\otimes N_r}$: $2^{-5N_r/2}5^{\|\mathbf a\oplus\mathbf b\oplus\mathbf x\cdot\mathbf y\|}$
-- statement:
--   For all bit strings $\mathbf a,\mathbf b,\mathbf x,\mathbf y\in\{0,1\}^{N_r}$,
--
--   $$
--   \mathrm{CHSH}^{\otimes N_r}(\mathbf a,\mathbf b,\mathbf x,\mathbf y)=2^{-5N_r/2}\,5^{\|\mathbf a\oplus\mathbf b\oplus\mathbf x\cdot\mathbf y\|},
--   $$
--
--   where $\mathbf x\cdot\mathbf y$ is the bitwise product, $\oplus$ the bitwise exclusive or, and $\|\cdot\|$ the number of ones. The exponent $M=\|\mathbf a\oplus\mathbf b\oplus\mathbf x\cdot\mathbf y\|$ counts the coordinates at which the CHSH condition $a_i\oplus b_i=x_iy_i$ fails; it governs every entrywise estimate in the proof of Lemma 2.
--
--   Differences from the source: none.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, pp.4–5

import Mathlib
import Definitions.Def_NoSignalPA_chshPow
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPA

/-- **The entries of `|CHSH⟩^{⊗Nr}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, pp. 4–5 (PDF pp. 4–5): "Using this notation we can write the
entries of the vector `|CHSH⟩^{⊗Nr}` as `CHSH^{⊗Nr}(a, b, x, y) = 2^{−5Nr/2} 5^{‖a⊕b⊕x·y‖}`".

For all bit strings `a, b, x, y` of length `Nr`, the entry of the tensor power of the table (2)
is `2^{−5Nr/2} · 5^{‖a ⊕ b ⊕ x·y‖}`, where `x·y` is the bitwise product, `⊕` the bitwise xor and
`‖·‖` the number of ones.

**Formalization Note.** `2^{−5Nr/2}` is a real power. -/
theorem chsh_tensor_entry {Nr : ℕ} (a b x y : Str Nr) :
    chshPow a b x y
      = (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2)
          * 5 ^ ones (fun i => xor (xor (a i) (b i)) (x i && y i)) := by sorry

end NoSignalPA
