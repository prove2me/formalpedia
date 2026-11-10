-- Prove2me | Theorems.Thm_GoldsteinMCSP_Hardness_equation_2
-- name    : GoldsteinMCSP.Hardness.equation_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:18.505533+00:00
-- url     : https://prove2.me/theorems/cb2b4f61-b1cd-42bb-95ab-1ef48e7ba67a
-- title:
--   Section 1.1, equation (2) — exact separator overhead
-- statement:
--   Let 𝒜=(A₁,...,A_l) and ℬ=(B₁,...,B_h) be related multisets of finite unsigned strings, with 1≤h≤l. Choose 2(l−1) pairwise distinct symbols x₁,y₁,...,x_{l−1},y_{l−1}, absent from every component. Form the strings A and B of equation (1): A inserts x_i y_i between consecutive A components; B inserts y_i x_i between consecutive B components and appends the remaining reversed separator pairs after B_h. Then
--
--   $$\operatorname{OPT}(A,B)=\operatorname{OPT}(𝒜,ℬ)+2(l-1).$$
--
--   Both optima are attained minimum block counts. No restriction to equal component counts, two-copy inputs or gadget instances is made. At l=1 the separator list is empty; empty component strings contribute no blocks.
--
--   Differences from the source:
--   - encoding: finite strings over a letter alphabet → finite lists of natural-number labels; reason: every finite input can be relabelled without changing multiplicities or contiguous blocks
--   - encoding: partitions into contiguous blocks → cut partitions with nonempty blocks, and the empty partition of an empty word; reason: empty blocks may be deleted without changing the optimum; this makes the standard cut-partition convention explicit
--   - encoding: multisets with 1 ≤ h ≤ l and 2(l−1) fresh separators → indexed component lists a,b and a list s of fresh pairs, with s.length+1=a.length; reason: indices retain multiplicities and express exactly the equation (1) domain, including an empty separator tail
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 1.1, equation (2), printed p. 6 (PDF p. 6); construction printed/PDF p. 5

import Definitions.Def_GoldsteinMCSP_Hardness_Strings

namespace GoldsteinMCSP.Hardness

theorem equation_2 (a b : Family) (s : List (ℕ × ℕ))
    (hr : related a.flatten b.flatten) (hb : 1 ≤ b.length)
    (hba : b.length ≤ a.length) (hs : s.length + 1 = a.length)
    (hf : freshSeparators a b s) :
    optimum (separated a s) (separated b (s.map Prod.swap)) =
      familyOptimum a b + 2*(a.length-1) := by sorry

end GoldsteinMCSP.Hardness
