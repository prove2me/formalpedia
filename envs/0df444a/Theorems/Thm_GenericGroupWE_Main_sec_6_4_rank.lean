-- Prove2me | Theorems.Thm_GenericGroupWE_Main_sec_6_4_rank
-- name    : GenericGroupWE.Main.sec_6_4_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:00.093193+00:00
-- url     : https://prove2.me/theorems/87b603bf-605e-4ef8-927e-9638cb4c5e53
-- title:
--   §6.4, Comparing the Ranks of the Two Tables — Low rank contradicts Lemma 6.2
-- statement:
--   Let $d\ge1$, $r=\max(1,\lfloor\sqrt{\log_2(N+2)}\rfloor)$ and $R=\binom{r+2d}{d}$. Let $p>\max(2^N,N(R^2+r))$ be prime. Suppose the quadratic system $q_s$ has no common Boolean zero. For the exact stack, weights and equation tests of §6, every nonzero matrix in the tested space satisfies
--
--   $$\operatorname{rank}A\ge R.$$
--
--   This is the full conclusion of the two-table comparison, stated directly for the source's explicitly defined space.
--
--   Differences from the source:
--   - encoding: finite indexed families and field residues → Fin-indexed families and ZMod prime fields; reason: zero-based indices and explicit finite carriers change no mathematical instance
--   - generalization: the quadratic system of the circuit, padded to N>=2 → any finite family of polynomials of total degree at most 2 with no common Boolean zero, also permitting N=0 and N=1; reason: the tests and the table argument use only the degree bound and the absence of a Boolean zero, so the statement specializes to the circuit system; unsatisfiable zero-variable systems force the tested space to be zero
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §6.4, Comparing the Ranks of the Two Tables, PDF p. 29 (printed p. 28).

import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main
open scoped BigOperators

theorem sec_6_4_rank (p N k d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (hp : max (2^N) (N * ((rankTarget N d)^2 + weightDegree N)) < p)
    (q : Fin k → MvPolynomial (Fin N) (ZMod p))
    (hq : ∀ s, (q s).totalDegree ≤ 2) (hunsat : NoBooleanZero q)
    (A : Matrix (StackRow N d) (BitMonomial N d) (ZMod p))
    (hmem : A ∈ testedSpace q) (hne : A ≠ 0) :
    rankTarget N d ≤ A.rank := by sorry

end GenericGroupWE.Main
