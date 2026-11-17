-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_0_coprime_classification__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_0_coprime_classification__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:26:47.423039+00:00
-- url     : https://prove2.me/theorems/6898b9ca-71f5-4ea4-932e-4d60ff156641
-- title:
--   Classify coprime offset-zero indices in residue class 6
-- statement:
--   For every index in the half-cycle, its two labels in the target are coprime exactly when the index is positive and has residue 1, 2, or 4 modulo 6.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_0_coprime_classification__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1 (n : ℕ) (hmod : n % 12 = 6) (j : Fin (n / 2)) :
    Nat.Coprime
      (KnodelPrimeCordial.labelF (2 * j.val))
      (KnodelPrimeCordial.labelF
        ((2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n)) ↔
    j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ) := by sorry
