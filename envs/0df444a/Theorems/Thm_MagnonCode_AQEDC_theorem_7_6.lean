-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_theorem_7_6
-- name    : MagnonCode.AQEDC.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:14.636198+00:00
-- url     : https://prove2.me/theorems/798cf548-9686-4dc9-bbc9-a59e7f9957a1
-- title:
--   Theorem 7.6 (corrected: bound $(C|A|(\max(r,s)+1)/n)^{|r-s|/2}$): off-diagonal matrix elements, any support
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $r\ne s$ with $r,s\le n-2$, let $A$ be any set of sites, and let $F$ act on $A$ with $\|F\|\le1$. Then
--
--   $$
--   |\langle\psi_r|F|\psi_s\rangle|\le\left(\frac{C\,|A|\,(\max(r,s)+1)}{n}\right)^{|r-s|/2}.
--   $$
--
--   Matrix elements of local operators between different magnon-states are therefore small when $|A|\max(r,s)\ll n$.
--
--   Differences from the source:
--   - correction: |⟨ψ_r|F⊗I|ψ_s⟩| = O(d/n^{|s−r|/2}) → (C |A| (max(r,s)+1)/n)^{|r−s|/2} with C absolute; reason: the printed bound is false: r = 0, s = 4, d = ⌊√n⌋, A the first d sites, F = |1^d⟩⟨χ| with χ the uniform unit vector on weight-4 strings and ‖F‖ = 1 gives a value about (d/n)², which is about d times d/n²; it is also not uniform in r at |r−s| = 2, which the printed proof of Theorem 7.9 needs
--   - generalization: F acting on the first d sites → F acting on any set A of sites; reason: the reduction to the first d sites (Lemma 7.4) is false, and A = first d sites specializes to the source
--   - encoding: F ∈ B((ℂ²)^{⊗d}), ‖F‖ ≤ 1, operator F ⊗ I → a matrix F on the whole space with IsLocalOn A F and ‖F‖ ≤ 1; reason: ‖F_A ⊗ I‖ = ‖F_A‖, so these are the same operators
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Theorem 7.6, p. 67

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_psiNorm
import Definitions.Def_MagnonCode_AQEDC_IsLocalOn

open scoped Matrix Matrix.Norms.L2Operator

namespace MagnonCode.AQEDC

/-- **Theorem 7.6, corrected** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 67): there is an absolute `C` such that for `r ≠ s`, both
at most `n − 2`, every set `A` of sites and every `F` acting on `A` with `‖F‖ ≤ 1`,
`|⟨ψ_r|F|ψ_s⟩| ≤ (C |A| (max(r, s) + 1) / n)^{|r − s|/2}`.

**Formalization Note** The printed bound `O(d / n^{|s−r|/2})` is false: `r = 0, s = 4, d = ⌊√n⌋`,
`F = |1^d⟩⟨χ|` with `χ` uniform on the weight-4 strings has value about `(d/n)²`. `C` precedes all
data, so it is absolute. `|r − s|` is taken in `ℝ` and the exponent is a real power; `r ≠ s` excludes
`0^0`. -/
theorem theorem_7_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ n r s : ℕ, r ≠ s → r + 2 ≤ n → s + 2 ≤ n →
      ∀ (A : Finset (Fin n)) (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        IsLocalOn A F → ‖F‖ ≤ 1 →
          ‖star (psiNorm n r) ⬝ᵥ F *ᵥ psiNorm n s‖ ≤
            (C * (A.card : ℝ) * ((max r s : ℕ) + 1 : ℝ) / (n : ℝ)) ^
              (|(r : ℝ) - (s : ℝ)| / 2) := by sorry

end MagnonCode.AQEDC
