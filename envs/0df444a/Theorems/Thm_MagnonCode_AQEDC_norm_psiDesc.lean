-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_norm_psiDesc
-- name    : MagnonCode.AQEDC.norm_psiDesc
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:27.757092+00:00
-- url     : https://prove2.me/theorems/13135745-4427-43fe-9b0e-2d47b084b568
-- title:
--   Eq. (84): norm and orthogonality of the descendants
-- statement:
--   Let $r,s\le n-2$. The descendant states satisfy
--
--   $$
--   \langle\Psi_r|\Psi_s\rangle=\delta_{r,s}\,\frac{n(n-2)!\,r!}{(n-2-r)!},
--   $$
--
--   and consequently the states $|\psi_r\rangle$ of Eq. (84) are orthonormal, $\langle\psi_r|\psi_s\rangle=\delta_{r,s}$.
--
--   This is what makes $\{\psi_r\}$ an orthonormal basis of the magnon code, as Corollary 3.4 requires.
--
--   Differences from the source:
--   - encoding: "their normalized versions which are given by" (84) → the norm formula for Ψ_r and orthonormality of ψ_r, both stated; reason: this is what the word "normalized" and the orthogonality sentence assert
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (84) and the sentence before it, p. 54; norm displayed on p. 68

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_psiNorm

open scoped Matrix

namespace MagnonCode.AQEDC

/-- **Eq. (84) and the text before it** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 54; the norm is displayed on p. 68): for
`r, s ≤ n − 2`, `⟨Ψ_r|Ψ_s⟩ = δ_{r,s} n (n − 2)! r! / (n − 2 − r)!`, so the states `ψ_r` of (84) are
orthonormal. -/
theorem norm_psiDesc (n r s : ℕ) (hr : r + 2 ≤ n) (hs : s + 2 ≤ n) :
    star (PsiDesc n r) ⬝ᵥ PsiDesc n s =
        (if r = s then
          (((n : ℝ) * (Nat.factorial (n - 2) : ℝ) * (Nat.factorial r : ℝ) /
            (Nat.factorial (n - 2 - r) : ℝ) : ℝ) : ℂ) else 0) ∧
      star (psiNorm n r) ⬝ᵥ psiNorm n s = if r = s then 1 else 0 := by sorry

end MagnonCode.AQEDC
