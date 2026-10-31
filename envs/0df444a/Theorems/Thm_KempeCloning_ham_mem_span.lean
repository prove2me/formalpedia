-- Prove2me | Theorems.Thm_KempeCloning_ham_mem_span
-- name    : KempeCloning.ham_mem_span
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:22.87107+00:00
-- url     : https://prove2.me/theorems/2fbc750b-1d64-4b23-9dfb-c75aa73abf26
-- title:
--   Sec. II C, p.5: $\mathcal H$ preserves superpositions of the $|\mathcal F_l\rangle$
-- statement:
--   Let $\gamma\in\mathbb R$, $m, N\in\mathbb N$, let $\mathcal H$ be the Hamiltonian (14) and $|\mathcal F_l\rangle$ the states (19). If $|\Phi\rangle$ is a superposition (complex linear combination) of $|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle$, then so is $\mathcal H|\Phi\rangle$:
--
--   $$|\Phi\rangle\in\operatorname{span}_{\mathbb C}\{|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle\}\;\Longrightarrow\;\mathcal H|\Phi\rangle\in\operatorname{span}_{\mathbb C}\{|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle\}.$$
--
--   This is the induction step of the paper's proof that the evolved state stays in this span.
--
--   Differences from the source:
--   - encoding: "a superposition of states $|\mathcal F_l\rangle$" → an element of $\operatorname{span}_{\mathbb C}\{|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle\}$; reason: $l$ ranges over $0,\dots,N$ as in (18), and a superposition is a linear combination
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
--   - reading: coupling constant $\gamma$, whose type the page does not state → $\gamma\in\mathbb R$; reason: (21) is printed with the same $\gamma$ on the term from (14) and on its h.c., which holds only for real $\gamma$, and the page absorbs phases into $\gamma$ (p.4)
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, paragraph after (20), p.5

import Definitions.Def_KempeCloning_ham
import Definitions.Def_KempeCloning_cloneState

namespace KempeCloning

/-- **Superpositions of the `|F_l⟩` are mapped by `H` to superpositions of the `|F_l⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, p.5: "Now we will show that if |Φ⟩ is
a superposition of states |F_l⟩ then H|Φ⟩ is so, too."

For every real `γ`, all `m, N`, and every `Φ` in the complex linear span of
`|F_0⟩, …, |F_N⟩`, the vector `H|Φ⟩` lies in the same span. -/
theorem ham_mem_span (γ : ℝ) (m N : ℕ) (Φ : FockVec)
    (hΦ : Φ ∈ Submodule.span ℂ (Set.range fun l : Fin (N + 1) => cloneState m N l)) :
    ham γ Φ ∈ Submodule.span ℂ (Set.range fun l : Fin (N + 1) => cloneState m N l) := by sorry

end KempeCloning
