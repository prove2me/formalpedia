-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_five_scan_comparison
-- name    : IntegerMatrixMortality.FixedImage.five_scan_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:15.561568+00:00
-- url     : https://prove2.me/theorems/5f4661b7-ed42-498d-8d90-04ba9075a104
-- title:
--   Lemma D.1 — Five-scan comparison and residue bound
-- statement:
--   Let p≥7 be prime, n≥1, 1≤b≤n, a=n−b and Q=a+1. In (D.2) a valid path with this chosen prefix reaches h₁ exactly when
--
--   $$b=4Q\quad\text{or}\quad Q<b<2Q.$$
--
--   Every such path gives T(x). For b=4Q, x=X_{a,4a+3} and n=5a+4. In the exceptional case x≠0 and its leading residue is 4, 3 or −1 according as 2b<3Q, 2b=3Q or 2b>3Q. Every valid finite prefix has local residue in Δ, including T(x), incorrect guesses and prefixes that never finish. These clauses are required to reject the false splits safely.
--
--   Differences from the source:
--   - encoding: the chosen prefix and comparison scans → a valid table walk whose first arrival at marker phase 3 occurs after b deletions; reason: this counts the exit deletion and retains every rejected valid prefix
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma D.1, PDF p. 25 / printed p. 23

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem five_scan_comparison
    (p n b : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hn : 1 ≤ n) (hb : 1 ≤ b) (hbn : b ≤ n) :
      let a := n-b
      let Q := a+1
      ((∃ y, CompletesWithGuess p contractionComparison b (some (unaryCode p n)) y) ↔
        b = 4*Q ∨ (Q < b ∧ b < 2*Q)) ∧
      (∀ y, CompletesWithGuess p contractionComparison b (some (unaryCode p n)) y →
        ∃ x : ℚ, y = T p (some x) ∧
          (b = 4*Q → x = intermediateCode p a (4*a+3) ∧ n = 5*a+4) ∧
          (Q < b ∧ b < 2*Q → x ≠ 0 ∧
            (2*b < 3*Q → LeadingResidue p x 4) ∧
            (2*b = 3*Q → LeadingResidue p x 3) ∧
            (3*Q < 2*b → LeadingResidue p x (-1)))) ∧
      ResiduePrefixes p contractionComparison (some (unaryCode p n)) delta := by sorry

end IntegerMatrixMortality.FixedImage
