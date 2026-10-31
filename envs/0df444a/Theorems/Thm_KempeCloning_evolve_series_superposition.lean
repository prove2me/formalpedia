-- Prove2me | Theorems.Thm_KempeCloning_evolve_series_superposition
-- name    : KempeCloning.evolve_series_superposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:28:09.62763+00:00
-- url     : https://prove2.me/theorems/5509c5f8-f310-4069-91ea-b5afed8b7459
-- title:
--   Sec. II C, p.5: $|\Psi(t)\rangle = \sum_p \frac{(-i\mathcal Ht)^p}{p!}|\Psi_{in}\rangle$ is a superposition of the $|\mathcal F_l\rangle$
-- statement:
--   Let $\gamma, t\in\mathbb R$ and $m, N\in\mathbb N$, let $\mathcal H$ be the Hamiltonian (14), $|\Psi_{in}\rangle = |m,0,0,0,N\rangle$ the initial state (13), $|\mathcal F_l\rangle$ the states (19), and $|\Psi(t)\rangle = e^{-i\mathcal Ht}|\Psi_{in}\rangle$ the evolved state of (18). Then:
--
--   1. $|\Psi(t)\rangle = \sum_p \frac{(-i\mathcal Ht)^p}{p!}|\Psi_{in}\rangle$, the series converging in the amplitude of every number state;
--   2. for every $p\in\mathbb N$, $\mathcal H^p|\Psi_{in}\rangle \in \operatorname{span}_{\mathbb C}\{|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle\}$;
--   3. $|\Psi(t)\rangle \in \operatorname{span}_{\mathbb C}\{|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle\}$.
--
--   This is the paper's step from the invariance of the span under $\mathcal H$ to the form (18) of the state.
--
--   **Formalization Note** Finite superpositions of number states carry no topology, so clause 1 is stated in each Fock coordinate. It ties the evolved state, defined by the matrix exponential of the compression of $\mathcal H$ to the sector (15), to the powers of $\mathcal H$ itself.
--
--   Differences from the source:
--   - encoding: the vector equality $|\Psi(t)\rangle = \sum_p \frac{(-i\mathcal Ht)^p}{p!}|\Psi_{in}\rangle$ → convergence of the series to $\langle n|\Psi(t)\rangle$ at every Fock index $n$; reason: finite superpositions carry no topology, and all terms lie in one finite-dimensional sector, where coordinatewise convergence is convergence
--   - generalization: "after a time interval $t$" ($t\ge0$) → every $t\in\mathbb R$; reason: the identities hold for every real $t$ and specialize to $t\ge0$
--   - reading: coupling constant $\gamma$, whose type the page does not state → $\gamma\in\mathbb R$; reason: (21) is printed with the same $\gamma$ on the term from (14) and on its h.c., which holds only for real $\gamma$, and the page absorbs phases into $\gamma$ (p.4)
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, paragraph after (20), p.5

import Definitions.Def_KempeCloning_evolve
import Definitions.Def_KempeCloning_initState
import Definitions.Def_KempeCloning_cloneState

namespace KempeCloning

/-- **The exponential series of `|Ψ(t)⟩`, and its superposition form.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, p.5: "Then, since
|Ψ(t)⟩ = e^{−iHt}|Ψin⟩ = Σ_p (−iHt)^p/p! |Ψin⟩ this implies that |Ψ(t)⟩ will be a superposition of
|F_l⟩."

For every real `γ, t` and all `m, N`:
1. `|Ψ(t)⟩ = Σ_p (−iHt)^p/p! |Ψ_in⟩`, the series converging in every Fock coordinate;
2. every term `H^p |Ψ_in⟩` lies in the complex linear span of `|F_0⟩, …, |F_N⟩`;
3. `|Ψ(t)⟩` lies in that span.

**Formalization Note.** `H^p` is the `p`-fold composition in `Module.End ℂ FockVec`. `FockVec` carries
no topology, so the series is stated coordinate by coordinate (`HasSum` in `ℂ` at each Fock index
`n`). Clause 1 ties `evolve`, defined by the matrix exponential of the compression to the sector
(15), to the powers of `ham` itself. -/
theorem evolve_series_superposition (γ t : ℝ) (m N : ℕ) :
    (∀ n : FockIndex,
      HasSum
        (fun p : ℕ =>
          ((-(Complex.I * (t : ℂ))) ^ p / (p.factorial : ℂ)) *
            ((ham γ ^ p) (initState m N)) n)
        ((evolve γ m N t) n)) ∧
    (∀ p : ℕ,
      (ham γ ^ p) (initState m N) ∈
        Submodule.span ℂ (Set.range fun l : Fin (N + 1) => cloneState m N l)) ∧
    evolve γ m N t ∈
      Submodule.span ℂ (Set.range fun l : Fin (N + 1) => cloneState m N l) := by sorry

end KempeCloning
