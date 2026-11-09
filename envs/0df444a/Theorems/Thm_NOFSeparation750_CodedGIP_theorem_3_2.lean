-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_3_2
-- name    : NOFSeparation750.CodedGIP.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:44:17.627529+00:00
-- url     : https://prove2.me/theorems/f509172d-acdf-4bcc-a483-e4d96c839ebb
-- title:
--   Theorem 3.2 — Garcia–Stichtenoth compatible codes with effective construction
-- statement:
--   Fix $k\ge2$ and any power of four $q$ satisfying $(32k)^2\le q\le(64k)^2$. Put $s=\sqrt q$ and $r_j=(q-s)s^j$ for every integer $j\ge0$. There exist ordered-basis linear codes $V_j,W_j\le\mathbb F_q^{r_j}$ such that
--   $$V_j^{\odot k}\subseteq W_j,\qquad \dim V_j\ge\frac{6r_j}{s},\qquad \operatorname{dist}(W_j)\ge\frac{3r_j}{4}.$$
--   The pair is $(6/s,3/4)$-compatible. For the fixed parameters there are uniform deterministic programs constructing both generator matrices and encoding messages for either code in time polynomial in $r_j$, with one polynomial bound for all $j$ and messages.
--
--   This supplies the effective code families underlying total coded GIP; mere finite existence of subspaces is insufficient.
--
--   Differences from the source:
--   - encoding: q a power of four, r_j=(q−√q)q^(j/2), and a fixed binary field representation → q=4^a with a≥1, s=2^a, b=2a, r_j=(4^a−2^a)(2^a)^j, and a b-bit-to-field bijection; reason: this parametrizes every allowed q exactly and avoids truncated fractional natural powers; any field of that cardinality is isomorphic to the source field
--   - encoding: deterministic polynomial-time algorithms → finite binary stack programs, actual halting executions, and one polynomial bound; reason: finite control and finite alphabets give the standard polynomial-time model; unary size headers have polynomial overhead
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 3.2, p.7; Appendix A.2–A.3, pp.12–13; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes

namespace NOFSeparation750.CodedGIP

/-- Theorem 3.2, p.7, including its uniform deterministic construction and encoding
clause (Appendix A, pp.12–13). q ranges over every allowed power of four. -/
theorem theorem_3_2 (k a : ℕ) (hk : 2 ≤ k) (ha : Allowed k a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 4 ^ a) :
    ∃ D : PairFamily F a, ∃ codec : (Fin (2 * a) → Bool) ≃ F,
      (∀ j, Compatible (D j).small.code (D j).large.code k
        (6 / (2 ^ a : ℝ)) (3 / 4)) ∧ EffectivePairFamily D codec := by sorry

end NOFSeparation750.CodedGIP
