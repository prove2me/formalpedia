-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_lemma_7_7
-- name    : MagnonCode.AQEDC.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:33.598054+00:00
-- url     : https://prove2.me/theorems/257b2924-9b7e-4106-ad6b-967bba1afe88
-- title:
--   Lemma 7.7, any support: the weight of $\psi_s$ on $|1\rangle^{\otimes A}$
-- statement:
--   There is an absolute constant $C>0$ such that for $1\le s\le n-2$ and every set $A$ of sites,
--
--   $$
--   \sum_{x:\ x_i=1\ \forall i\in A}|\psi_s(x)|^2\ \ge\ 1-\frac{C\,|A|\,s}{n}.
--   $$
--
--   The left side is the probability of finding all qubits of $A$ in the state $|1\rangle$ in $\psi_s$. For $A$ the first $d$ sites it equals $\langle1|^{\otimes d}(\operatorname{tr}_{n-d}|\psi_s\rangle\langle\psi_s|)|1\rangle^{\otimes d}$. So local reduced states of low descendants are close to $|1\rangle\langle1|^{\otimes|A|}$.
--
--   Differences from the source:
--   - generalization: the first d sites → any set A of sites; reason: Lemma 7.4 is false, so Theorem 7.9 needs arbitrary supports; A = first d sites specializes to the source
--   - encoding: for all s ∈ [n] → 1 ≤ s ≤ n − 2; reason: ψ_s is defined by (84) only for s ≤ n − 2, and [n] starts at 1
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Lemma 7.7, p. 68

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_psiNorm

namespace MagnonCode.AQEDC

/-- **Lemma 7.7, any support** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 68): there is an absolute `C` such that for
`1 ≤ s ≤ n − 2` and every set `A` of sites, the weight of `ψ_s` on "every site of `A` is `|1⟩`" is
at least `1 − C |A| s / n`.

**Formalization Note** The sum `Σ_{x : x|_A = 1} |ψ_s(x)|²` is the printed
`⟨1|^{⊗d} (tr_{n−d} |ψ_s⟩⟨ψ_s|) |1⟩^{⊗d}` when `A` is the first `d` sites. The printed range `s ∈ [n]`
becomes `1 ≤ s ≤ n − 2`, where `ψ_s` is defined by (84). -/
theorem lemma_7_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ n s : ℕ, 1 ≤ s → s + 2 ≤ n → ∀ A : Finset (Fin n),
      1 - C * (A.card : ℝ) * (s : ℝ) / (n : ℝ) ≤
        ∑ x ∈ Finset.univ.filter (fun x : Fin n → Fin 2 => ∀ i ∈ A, x i = 1),
          ‖psiNorm n s x‖ ^ 2 := by sorry

end MagnonCode.AQEDC
