-- Prove2me | Theorems.Thm_NecklacePPAD_Main_lemma_4_5
-- name    : NecklacePPAD.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:08:24.071856+00:00
-- url     : https://prove2.me/theorems/5838b570-fe96-4191-b127-8339c6c84803
-- title:
--   Lemma 4.5 (readings) — a determined reading labels its segment; R_c(i) = ⊥ iff S_c = κ, else [S_c < κ]
-- statement:
--   In the situation of Lemma 4.3 and for $i\in[1,m_c-1]$: (a) if $R_c(i)\neq\bot$, then every position in segment $i$ of $c$ has label $R_c(i)$; (b) let $\kappa=i-b_c+s_c$ if $\tau(c)=0$ and $\kappa=b_c-i$ if $\tau(c)=1$ (integers); then $R_c(i)=\bot$ if $S_c=\kappa$, and $R_c(i)=[S_c<\kappa]$ otherwise.
--
--   Differences from the source:
--   - encoding: 1-based positions [N], labels in {0,1}, ℓ(1) = 0 → 0-based positions, labels Bool (true = 1), lab ℓ 0 = false; reason: Lean indexing; the same labellings
--   - encoding: B(c) a set of consecutive positions → an interval [lo c, hi c] with lo c ≤ hi c < N; reason: B(c) holds more than b_c ≥ 0 beads of colour c, so it is nonempty, and a nonempty set of consecutive positions is such an interval
--   - encoding: a set C of n colours; balanced: exactly b_c of the 2b_c positions of colour c have label 1 → colours Fin n; 2·#{q : a_q = c, ℓ q} = count c; reason: same necklaces; the count of colour c is 2b_c
--   - reading: "in the situation of Lemma 4.3", with R_c(i) defined (Definition 4.4) for i ∈ [1, m_c − 1] → hypotheses 1 ≤ i and i + 1 ≤ m_c; reason: the domain of Definition 4.4
--   - encoding: values {0, 1, ⊥}, the indicator [S_c < κ], κ an integer → PVal (published), PVal.ofBool (decide (S_c < κ)), κ : ℤ; reason: same values; κ can be negative when τ(c) = 0
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Lemma 4.5, p. 6 (PDF 8)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Reading

set_option autoImplicit false

namespace NecklacePPAD.Main

open Blocks LpBallVI.Affine

/-- **Lemma 4.5 (readings)** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, sha256 d5b5449c…,
p. 6 (PDF 8)). In the situation of Lemma 4.3, for `i ∈ [1, m_c − 1]`:
(a) if `R_c(i) ≠ ⊥`, every position in segment `i` of `c` has label `R_c(i)`;
(b) with `κ = i − b_c + s_c` if `τ(c) = 0` and `κ = b_c − i` if `τ(c) = 1` (integers),
`R_c(i) = ⊥` if `S_c = κ` and `R_c(i) = [S_c < κ]` otherwise. -/
theorem lemma_4_5 (a : Necklace) (B : Blocks a.n) (ha : a.IsNecklace) (hB : a.IsRigid B)
    (ℓ : Fin a.N → Bool) (hℓ : a.IsSplit ℓ) (h0 : a.lab ℓ 0 = false) (c : Fin a.n)
    (hlo : a.beads[B.lo c]? = some c) (hhi : a.beads[B.hi c]? = some c)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ homeCount a B c) :
    (reading a B ℓ c i ≠ .bot →
      ∀ q, InSegment a B c i q → PVal.ofBool (a.lab ℓ q) = reading a B ℓ c i) ∧
    (let κ : ℤ := if B.tau c = 0 then (i : ℤ) - a.half c + sensorCount a B c
        else (a.half c : ℤ) - i
     reading a B ℓ c i =
       if (sensorOnes a B ℓ c : ℤ) = κ then .bot
       else PVal.ofBool (decide ((sensorOnes a B ℓ c : ℤ) < κ))) := by sorry

end NecklacePPAD.Main
