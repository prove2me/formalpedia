-- Prove2me | Theorems.Thm_HighMagSampling_SK_downUp_reversible
-- name    : HighMagSampling.SK.downUp_reversible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:27:47.666317+00:00
-- url     : https://prove2.me/theorems/99ac73d5-2568-48b2-91c6-43514bf2846b
-- title:
--   §2.2 — the down-up walk $\mathcal T^{\mathrm{DU},\pi}$ on $\mathcal X^d_k$ is reversible with stationary measure $\pi$
-- statement:
--   Let $d\ge1$, $k\in[d]$, and let $\pi$ be any finite measure on the Hamming slice $\mathcal X^d_k$ (in particular any $\pi\in\mathcal P(\mathcal X^d_k)$). Then the down-up walk $\mathcal T^{\mathrm{DU},\pi}$ is reversible with stationary measure $\pi$:
--   $$\mathcal T^{\mathrm{DU},\pi}\pi=\pi\qquad\text{and}\qquad \pi(S)\,\mathcal T^{\mathrm{DU},\pi}_S(S')=\pi(S')\,\mathcal T^{\mathrm{DU},\pi}_{S'}(S)\ \ \text{for all }S,S'\in\mathcal X^d_k.$$
--
--   The paper calls this standard (citing Kaufman–Oppenheim, Definitions 6 and 7 and Corollary 11) and uses it to apply the Poincaré-to-mixing bound of Lemma 1 to the down-up walk.
--
--   **Formalization Note.** Detailed balance is stated for measurable sets (Mathlib's `Kernel.IsReversible`), which on the finite discrete slice is the pointwise identity above. No full-support assumption is made, as on the page ("defined for any measure $\pi$ supported on $\mathcal X^d_k$").
--
--   Differences from the source:
--   - encoding: $\mathcal X^d_k$ as $\pm1$ vectors → `Slice d k`, the $k$-subsets of `Fin d`; reason: the paper's own bijection $x\mapsto\mathrm{set}(x)$, same instances.
--   - encoding: the up step from a $\pi$-null state with vanishing normaliser is undefined on the page → that term of the kernel is $0$; reason: Lean needs a value; such states carry no $\pi$-mass, and every state of positive mass has a probability transition.
--   - generalization: $\pi$ a measure supported on $\mathcal X^d_k$, read in the paper's §2.2 setting as $\pi\in\mathcal P(\mathcal X^d_k)$ → any finite measure on the slice; reason: the walk depends on $\pi$ only up to scale and both stationarity and detailed balance are linear in $\pi$, so the probability case is the special case of total mass $1$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 10, §2.2, reversibility of the down-up walk

import Mathlib
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp

open MeasureTheory ProbabilityTheory

namespace HighMagSampling.SK

/-- §2.2, p. 10: for every (finite) measure `π` on the slice `X^d_k`, `k ∈ [d]`, the down-up
walk `T^{DU,π}` is reversible with stationary measure `π`. -/
theorem downUp_reversible (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (π : Measure (Slice d k))
    [IsFiniteMeasure π] : IsReversibleWith (downUp π) π := by sorry

end HighMagSampling.SK
