-- Prove2me | Theorems.Thm_GenericGroupWE_Main_prop_3_3
-- name    : GenericGroupWE.Main.prop_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:47.678198+00:00
-- url     : https://prove2.me/theorems/543798b3-75eb-4d92-8259-df623dd318e0
-- title:
--   Proposition 3.3 — Correctness of decryption
-- statement:
--   Let $n\ge2$, $m\ge16n$, and let $p\ge2^m$ be prime. For any valid certificate $\sum_j a_jM_j=uv^T\ne0$ with $v$ Boolean, and either encrypted message, the explicit bounded sampler and valid-witness oracle decryption core satisfy
--
--   $$\Pr[\mathrm{Dec}(\mathrm{Enc}(\beta))\ne\beta]\le\delta+m^22^{-m}\le2^{-n}.$$
--
--   The abort outcome is included; decryption returns zero there, so aborts can be errors for message one. Both inequalities are part of the item.
--
--   Differences from the source:
--   - generalization: a satisfying witness of the source reduction and a prime below 2^(m+1) → any valid rank-one Boolean-right-factor certificate and any prime p>=2^m; reason: correctness needs the certificate and lower prime bound, not the NP label, basis independence, NO-case rank gap or upper prime bound
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Proposition 3.3, PDF p. 9 (printed p. 8).

import Definitions.Def_GenericGroupWE_Main_Scheme

namespace GenericGroupWE.Main
open scoped BigOperators

theorem prop_3_3 (n m : ℕ) (hn : 2 ≤ n) (hm : 16*n ≤ m) (p : PrimeOrder)
    (hp : 2^m ≤ p.val) (B : MatrixBundle m p) (w : RankOneCertificate B)
    (hw : w.Valid) (message : Bool) :
    probability (boundedEncryption B n message) (fun C => schemeDecryption w C ≠ some message) ≤
      samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ∧
    samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ≤ (2 : ℝ)^(-(n : ℝ)) := by sorry

end GenericGroupWE.Main
