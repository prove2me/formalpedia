-- Prove2me | Theorems.Thm_MainResults_mainTheorem
-- name    : MainResults.mainTheorem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T08:56:12.729859+00:00
-- url     : https://prove2.me/theorems/df90e706-4a27-4a83-ba7f-ae4d21618f9b
-- title:
--   Theorem 1: uniform subexponential counting of satisfying assignments
-- statement:
--   With no hypotheses, this theorem asserts that there exist one Boolean-input/Boolean-output Mathlib $\operatorname{TM2ComputableAux}$ machine $M$ and one natural number $C$, with every machine alphabet $M.\mathrm{tm}.\Gamma(i)$ finite, such that for every pair of natural numbers $k,n$ and every CNF formula $\varphi$ represented as a finite ordered list of finite ordered literal lists over the $n$ variables, if $k\ge1$, every clause has length at most $k$, the outer clause list has no repeated literal lists, the number of clauses $m=\operatorname{length}(\varphi)$ is at least $2$, $n\ge4$, and each variable occurs in at least one literal, then $M$ satisfies the library predicate $\operatorname{TM2OutputsInTime}$ with this input, successful output, and natural time bound: the input is $k$ true bits and false, then $n$ true bits and false, then exactly $k$ literal slots for each clause, each slot comprising $\operatorname{Nat.log2}(2n)+1$ bits in increasing bit-position order of zero for a missing literal or $2i+1+\operatorname{toNat}(b)$ for literal $(i,b)$; the output is exactly $n+1$ bits, again in increasing bit-position order, of the number of Boolean assignments to all $n$ variables such that each clause contains a literal $(i,b)$ with the assignment at $i$ equal to $b$; and the time bound is $\left\lfloor2^{C\min\left(km/\sqrt{\log_2m},\;k^2n\log_2(\log_2n)/\sqrt{\log_2n}\right)}\right\rfloor_+$. Input and output bits are transported using $M$'s inverse alphabet maps. The same machine and the same constant must work for all $k,n,\varphi$ meeting these conditions; the stated bound has no additional multiplicative factor outside the exponential. The output represents the count exactly, because it is between $0$ and $2^n$, inclusive. Clause repetition is excluded only as equality of ordered literal lists, so different permutations can count as different clauses; repeated literals, tautological clauses, and an empty clause are allowed, and an empty clause forces the count to zero. The hypotheses $m\ge2$ and $n\ge4$ ensure the displayed logarithmic denominators are positive; the theorem promises nothing for inputs failing any stated restriction. The natural constant $C$ may be zero, in which case the displayed bound is $1$. The computation and time bound are in the specified Mathlib TM2 model; no statement about a different machine model is included.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/Solution.lean

import Definitions.Def_MainResults

theorem MainResults.mainTheorem : MainResults.MainTheorem := by sorry
