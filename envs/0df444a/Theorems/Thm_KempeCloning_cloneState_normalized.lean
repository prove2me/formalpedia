-- Prove2me | Theorems.Thm_KempeCloning_cloneState_normalized
-- name    : KempeCloning.cloneState_normalized
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:35.553633+00:00
-- url     : https://prove2.me/theorems/058881c8-e1fb-41e1-8156-48ba73e72e87
-- title:
--   Sentence after (19): $|\mathcal F_l\rangle$ is normalized with $m+l$ photons
-- statement:
--   Let $m, N\in\mathbb N$ and $0\le l\le N$, and let $|\mathcal F_l\rangle$ be the state (19). Then
--
--   1. $|\mathcal F_l\rangle$ is normalized: $\langle\mathcal F_l|\mathcal F_l\rangle = 1$;
--   2. $|\mathcal F_l\rangle$ has $m+l$ photons in total: every number state occurring in it with nonzero amplitude has $n_{a_1} + n_{a_2} = m + l$.
--
--   Together with the fidelity formula (20), this identifies $|\mathcal F_l\rangle$ as the output state of an $m\to m+l$ photon cloner.
--
--   Differences from the source:
--   - encoding: "a state of the system with $m+l$ photons in total" → every number state in the support of $|\mathcal F_l\rangle$ has $n_{a_1}+n_{a_2} = m+l$; reason: this is what a definite total photon number in modes $a_1, a_2$ means ("total means counting photons in mode a1 and a2", p.5)
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, sentence after (19), p.5

import Definitions.Def_KempeCloning_cloneState
import Definitions.Def_KempeCloning_normSq

namespace KempeCloning

/-- **`|F_l⟩` is a normalized state with `m + l` photons.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, sentence after (19), p.5: "|F_l⟩ is a
normalized state of the system with m + l photons in total."

For all `m, N` and every `l ≤ N`:
1. `⟨F_l|F_l⟩ = 1`;
2. every Fock basis state occurring in `|F_l⟩` has `n_{a1} + n_{a2} = m + l` photons. -/
theorem cloneState_normalized (m N l : ℕ) (hl : l ≤ N) :
    normSq (cloneState m N l) = 1 ∧
      ∀ n ∈ (cloneState m N l).support, n Mode.a1 + n Mode.a2 = m + l := by sorry

end KempeCloning
