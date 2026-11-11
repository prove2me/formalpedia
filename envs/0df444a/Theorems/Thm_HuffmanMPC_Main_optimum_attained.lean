-- Prove2me | Theorems.Thm_HuffmanMPC_Main_optimum_attained
-- name    : HuffmanMPC.Main.optimum_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:54.995641+00:00
-- url     : https://prove2.me/theorems/3a3511d0-cc3b-49da-89d1-a56285198501
-- title:
--   §2 — the minimum encoded length is attained and equals the real infimum over prefix-free codes
-- statement:
--   Let $A=(f_1,\dots,f_m)$ be a list of positive frequencies. The minimum in
--   $$\mu(A)=\min_{C\ \text{prefix-free}}\sum_{i=1}^m f_i\,|C(i)|$$
--   is attained by some prefix-free binary code, and it coincides with the infimum of the weighted lengths $\sum_i f_i|C(i)|$ over all prefix-free codes, computed in the reals.
--
--   This justifies writing $\mu$ as a minimum, as the source does, and identifies it with the published quantity `FuchsThesis.Coding.minLength` evaluated at the raw (unnormalized) frequencies.
--
--   Differences from the source:
--   - encoding: $\mu$ written as a minimum over prefix-free codes → attainment of the natural-number infimum, and its equality with the published real infimum `minLength` at the weights $f_i$; reason: the same quantity in two representations; attainment is what the word min asserts
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, §2, definition of $\mu(T)$, p. 2 (PDF 3)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

theorem optimum_attained (a : Frequencies) (ha : Positive a) :
    (∃ c : Fin a.length → List Bool,
      FuchsThesis.Coding.IsInstantaneous c ∧ codeCost a c = optimum a) ∧
    (optimum a : ℝ) = FuchsThesis.Coding.minLength (fun i : Fin a.length => (a[i] : ℝ)) := by sorry

end HuffmanMPC.Main
