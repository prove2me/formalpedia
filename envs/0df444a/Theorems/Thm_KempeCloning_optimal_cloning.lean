-- Prove2me | Theorems.Thm_KempeCloning_optimal_cloning
-- name    : KempeCloning.optimal_cloning
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:28:17.491905+00:00
-- url     : https://prove2.me/theorems/a0ba42ba-2416-4b2b-94d1-a147c64e025a
-- title:
--   Eqs. (18)–(20): $e^{-i\mathcal Ht}|\Psi_{in}\rangle = \sum_{l=0}^N f_l|\mathcal F_l\rangle$ with $|\mathcal F_l\rangle$ normalized $m+l$-photon states of fidelity $\frac{m(m+2)+l(m+1)}{(m+l)(m+2)}$
-- statement:
--   Consider $m$ photons in mode $a_1$ and $N$ excited $\Lambda$-atoms, in the oscillator model of the paper: five modes $a_1, a_2, b_1, b_2, c$, the Hamiltonian (14)
--
--   $$\mathcal H = \gamma\,(a_1 b_2 - a_2 b_1)\,c^\dagger + \mathrm{h.c.},\qquad \gamma\in\mathbb R,$$
--
--   the initial state (13) $|\Psi_{in}\rangle = |m,0,0,0,N\rangle$, and the states (19)
--
--   $$|\mathcal F_l\rangle = \binom{m+l+1}{l}^{-\frac12}\sum_{i=0}^{l}(-1)^i\sqrt{\binom{m+l-i}{m}}\;\big|(m+l-i)_{a_1}, i_{a_2}, i_{b_1}, (l-i)_{b_2}, (N-l)_c\big\rangle ,\qquad 0\le l\le N.$$
--
--   For all $m, N\in\mathbb N$ and all real $\gamma$ and $t$:
--
--   1. the evolved state is a superposition of the $|\mathcal F_l\rangle$: there are $f_0,\dots,f_N\in\mathbb C$ with
--   $$|\Psi(t)\rangle = e^{-i\mathcal Ht}|\Psi_{in}\rangle = \sum_{l=0}^{N} f_l\,|\mathcal F_l\rangle ; \tag{18}$$
--   2. each $|\mathcal F_l\rangle$, $0\le l\le N$, is normalized;
--   3. each $|\mathcal F_l\rangle$, $0\le l\le N$, has $m+l$ photons in total ($n_{a_1}+n_{a_2}=m+l$ on its support);
--   4. for $0\le l\le N$ with $m+l\ge1$, the mean relative frequency of photons in the correct mode $a_1$ in $|\mathcal F_l\rangle$ is
--   $$F_l = \binom{m+l+1}{l}^{-1}\sum_{i=0}^{l}\binom{m+l-i}{m}\frac{m+l-i}{m+l} = \frac{m(m+2)+l(m+1)}{(m+l)(m+2)} . \tag{20}$$
--
--   So stimulated emission of $N$ $\Lambda$-atoms produces a superposition, over the number $l$ of additional photons, of states with the fidelity of the optimal universal $m\to m+l$ cloner; measuring the number of atoms left in the excited state selects one $l$.
--
--   **Formalization Note** $e^{-i\mathcal Ht}|\Psi_{in}\rangle$ is the matrix exponential of the compression of $\mathcal H$ to the finite, $\mathcal H$-invariant sector (15) that contains $|\Psi_{in}\rangle$. The coefficients $f_l$ are asserted to exist, as in the paper, which does not compute them.
--
--   Differences from the source:
--   - reading: "the system defined by (13) and (14) indeed realizes optimal cloning" → the four clauses (18), normalization and photon number of $|\mathcal F_l\rangle$, and (20); reason: the paper's "optimal" is the identification of (20) with the optimal universal cloning fidelity of its reference [5], which it cites and does not prove; the universality of the cloner is a remark of the page drawn from the symmetry of (14) and of the initial atomic state (pp.3, 5), and is not a clause here
--   - encoding: the five-mode Fock space and $e^{-i\mathcal Ht}$ → finite superpositions of number states, and the matrix exponential of the compression of (14) to the $\mathcal H$-invariant sector (15); reason: the sector is finite-dimensional, contains $|\Psi_{in}\rangle$ and is $\mathcal H$-invariant, so this is the Schrödinger evolution $\sum_p (-i\mathcal Ht)^p/p!\,|\Psi_{in}\rangle$
--   - encoding: coefficients $f_l(t)$ → for each fixed $\gamma, m, N, t$ there exist coefficients $f_l\in\mathbb C$; reason: the paper asserts only the form of the state ("the form of the coefficients $f_l(t)$ didn't play any role"), which is a statement for each $t$
--   - generalization: "after a time interval $t$" ($t\ge0$) → every $t\in\mathbb R$; reason: the decomposition holds for every real $t$ and specializes to $t\ge0$
--   - encoding: "with $m+l$ photons in total" → every number state in the support of $|\mathcal F_l\rangle$ has $n_{a_1}+n_{a_2}=m+l$; reason: this is what a definite total photon number in modes $a_1, a_2$ means
--   - encoding: the fraction $(m+l-i)/(m+l)$, undefined at $m+l=0$ → hypothesis $0 < m+l$; reason: excludes only the case in which the page's fraction is $0/0$
--   - encoding: fidelity "given by the mean relative frequency of photons in the correct mode" → $\sum_n |\psi(n)|^2\, n_{a_1}/(n_{a_1}+n_{a_2})$; reason: the page's notion written out; $|\mathcal F_l\rangle$ is normalized, so no division by the norm is needed
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
--   - reading: coupling constant $\gamma$, whose type the page does not state → $\gamma\in\mathbb R$; reason: (21) is printed with the same $\gamma$ on the term from (14) and on its h.c., which holds only for real $\gamma$, and the page absorbs phases into $\gamma$ (p.4)
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, (18)–(20), p.5

import Definitions.Def_KempeCloning_evolve
import Definitions.Def_KempeCloning_cloneState
import Definitions.Def_KempeCloning_normSq
import Definitions.Def_KempeCloning_relFreqA1

namespace KempeCloning

/-- **Optimal cloning with stimulated emission: `e^{−iHt}|Ψ_in⟩ = Σ_{l=0}^{N} f_l(t)|F_l⟩`, and each
`|F_l⟩` is a normalized `m + l`-photon state of fidelity `(m(m+2) + l(m+1))/((m+l)(m+2))`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, (18)–(20), p.5: "We are now going to
show that the system defined by (13) and (14) indeed realizes optimal cloning for arbitrary N and m.
[…] We will show that the general form of the state vector after a time interval t is
|Ψ(t)⟩ = e^{−iHt}|Ψin⟩ = Σ_{l=0}^{N} f_l(t)|F_l⟩, (18) […] |F_l⟩ is a normalized state of the system
with m + l photons in total. […] Therefore F_l = (m(m + 2) + l(m + 1))/((m + l)(m + 2)) (20)".

For all `m, N : ℕ` and all real `γ, t`, with `H` the Hamiltonian (14), `|Ψ_in⟩ = |m,0,0,0,N⟩` (13)
and `|F_l⟩` the states (19):
1. there are complex coefficients `f_l` with `e^{−iHt}|Ψ_in⟩ = Σ_{l=0}^{N} f_l |F_l⟩` (18);
2. every `|F_l⟩`, `l ≤ N`, is normalized;
3. every `|F_l⟩`, `l ≤ N`, contains only Fock states with `m + l` photons in modes `a₁, a₂`;
4. for `l ≤ N` with `m + l ≥ 1`, the mean relative frequency of photons in `a₁` in `|F_l⟩` equals
   `binom(m+l+1, l)^{−1} Σ_{i=0}^{l} binom(m+l−i, m) (m+l−i)/(m+l)` and
   `(m(m+2) + l(m+1))/((m+l)(m+2))` (20).

**Formalization Note.** `e^{−iHt}|Ψ_in⟩` is `evolve γ m N t`: the matrix exponential of the
compression of (14) to its invariant sector (15). The coefficients `f_l` may depend on `γ, m, N, t`;
only their existence is asserted, as in the paper ("the form of the coefficients f_l(t) didn't play
any role in our proof"). -/
theorem optimal_cloning (m N : ℕ) (γ t : ℝ) :
    (∃ f : ℕ → ℂ, evolve γ m N t = ∑ l ∈ Finset.range (N + 1), f l • cloneState m N l) ∧
    (∀ l : ℕ, l ≤ N → normSq (cloneState m N l) = 1) ∧
    (∀ l : ℕ, l ≤ N → ∀ n ∈ (cloneState m N l).support, n Mode.a1 + n Mode.a2 = m + l) ∧
    (∀ l : ℕ, l ≤ N → 0 < m + l →
      relFreqA1 (cloneState m N l) =
          ((m + l + 1).choose l : ℝ)⁻¹ *
            ∑ i ∈ Finset.range (l + 1),
              ((m + l - i).choose m : ℝ) * (((m + l - i : ℕ) : ℝ) / ((m : ℝ) + l)) ∧
        relFreqA1 (cloneState m N l) =
          ((m : ℝ) * (m + 2) + l * (m + 1)) / (((m : ℝ) + l) * (m + 2))) := by sorry

end KempeCloning
