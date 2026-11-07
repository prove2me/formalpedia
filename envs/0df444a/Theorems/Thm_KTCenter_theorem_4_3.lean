-- Prove2me | Theorems.Thm_KTCenter_theorem_4_3
-- name    : KTCenter.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:31.96421+00:00
-- url     : https://prove2.me/theorems/96686c78-a793-4ffb-92f6-6529efbfcbba
-- title:
--   Theorem 4.3 — a small set of inputs reveals all but $\delta R^*$ optimal inversions per input
-- statement:
--   Relabel so that $\rho=\pi_1=(1,\dots,d)$, and fix an optimal center $\sigma^*$. For every real $\delta>0$ there is an index set $J\subseteq[n]$ with $1\in J$ and $|J|\le r=1+\lceil1/\delta\rceil$ such that
--
--   $$|U_J\cap\mathrm{Inv}(\pi_i)|\le\delta R^*\qquad(i\in[n]),\qquad(10)$$
--
--   where $U_J=\mathrm{Inv}(\sigma^*)\setminus E_J$.
--
--   A constant number of inputs thus determines the optimal center's pair orders up to an error the radius can absorb.
--
--   Differences from the source:
--
--   - encoding: candidates relabeled by their position in the first input, so ρ = π₁ = (1, …, d) (§4.1) → hypothesis `I.π I.first = 1` on the input list; reason: the relabeling preserves all distances and is undone at the end (p.17); the statements of §§4–5 are about relabeled inputs
--   - reading: "Fix an optimal center σ*" (p.17), after which J is chosen → ∀ optimal σ*, ∃ J; reason: U_J depends on σ*; the proof works for any fixed optimal center
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 4.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_InversionUnion

namespace KTCenter

/-- **Theorem 4.3** (A small set of input rankings), p.18 (PDF p.20).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** On relabeled inputs, `π₁ = 1` (§4.1). `σ*` is any optimal center, fixed before
`J` ("Fix an optimal center σ*", p.17). `δ` is real. -/
theorem theorem_4_3 (I : Instance) (hρ : I.π I.first = 1) (σs : Equiv.Perm (Fin I.d))
    (hσ : obj I σs = optRadius I) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : Finset (Fin I.n), I.first ∈ J ∧ J.card ≤ 1 + ⌈1 / δ⌉₊ ∧
      ∀ i : Fin I.n, (((UJ I J σs) ∩ Inv (I.π i)).card : ℝ) ≤ δ * (optRadius I : ℝ) := by sorry

end KTCenter
