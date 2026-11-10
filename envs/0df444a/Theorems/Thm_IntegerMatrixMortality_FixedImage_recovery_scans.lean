-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_recovery_scans
-- name    : IntegerMatrixMortality.FixedImage.recovery_scans
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:17.257912+00:00
-- url     : https://prove2.me/theorems/f063d405-f154-4424-b2ab-e450573dce4f
-- title:
--   Lemma D.3 — Recovery scans reject wrong guesses
-- statement:
--   Let p≥7 be prime, m∈{2,3}, Q≥1 and 1≤r_{m−1}<⋯<r₁<mQ. Put H=Σ_{j=1}^m p^{jQ}−Σ_{i=1}^{m−1}p^{rᵢ} and z=H/[p(1−H)]. All m marker-one scans complete in V exactly when
--
--   $$r_i=(m-i)Q\quad(1\le i<m).$$
--
--   For these guesses z=z_{mQ−1}, and each scan preserves it. Throughout the recovery graph starting from X_{Q−1,mQ−1}, the input and every complete generator output on every valid prefix have residue in {−1,0,1,2}, including prefixes of incorrect guesses. The subtraction in H takes place over the rationals.
--
--   Differences from the source:
--   - encoding: strictly decreasing positive integer exponents → a decreasing list of natural exponents with length m−1 and explicit positivity bounds; reason: the represented integer guesses coincide exactly, with H computed in ℚ
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma D.3, PDF p. 28 / printed p. 26

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem recovery_scans
    (p m Q : ℕ) (rs : List ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hm : m ∈ ({2,3} : Finset ℕ)) (hQ : 1 ≤ Q) (hl : rs.length = m-1)
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r < m*Q) (ho : rs.Pairwise (· > ·)) :
      let z := recoveryCandidate p m Q rs
      ((∃ y, MarkerScans p 1 m z y) ↔
        rs = (List.range (m-1)).map (fun i => (m-(i+1))*Q)) ∧
      (rs = (List.range (m-1)).map (fun i => (m-(i+1))*Q) →
        z = some (unaryCode p (m*Q-1)) ∧
        (∀ y, MarkerScan p 1 z y ↔ y = z)) ∧
      ResiduePrefixes p (recoveryModule m)
        (some (intermediateCode p (Q-1) (m*Q-1))) {-1,0,1,2} := by sorry

end IntegerMatrixMortality.FixedImage
