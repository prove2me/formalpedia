-- Prove2me | Theorems.Thm_FriezeKannan_PseudoReg_claim_50
-- name    : FriezeKannan.PseudoReg.claim_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:58.393915+00:00
-- url     : https://prove2.me/theorems/3aa0e279-59be-48cc-9fef-cfeb556ce18b
-- title:
--   (50), p. 204 — the coarsest partition refining all R_t, C_t of a cut decomposition with error εn² is 2ε-pseudo-regular
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $n=|V|$ vertices and adjacency matrix $\mathbf A$, and let $\epsilon$ be a real number. Let $\mathbf D^{(t)}=\mathrm{CUT}(R_t,C_t,d_t)$, $t=1,\dots,s$, be cut matrices with $R_t,C_t\subseteq V$ and $d_t\in\mathbb R$, and $\mathbf D=\mathbf D^{(1)}+\dots+\mathbf D^{(s)}$. Suppose the decomposition has error at most $\epsilon n^2$ in the cut norm:
--   $$|\mathbf A(S,T)-\mathbf D(S,T)|\le\epsilon n^2\qquad\text{for all }S,T\subseteq V.$$
--   Let $\mathcal P=V_1,\dots,V_k$ be the coarsest partition of $V$ into subsets such that each $R_t$ or $C_t$ is a union of parts of the partition. Then
--   $$\text{the partition }V_1,\dots,V_k\text{ is }2\epsilon\text{-pseudo-regular,}$$
--   that is, $|\Delta_{\mathcal P}(S,T)|\le 2\epsilon n^2$ for all disjoint $S,T\subseteq V$.
--
--   Combined with a cut decomposition of width $s$, whose atom partition has at most $4^s$ parts, this produces pseudo-regular partitions of every graph with a number of parts depending only on $\epsilon$: a weak form of Szemerédi's regularity lemma.
--
--   **Formalization Note.** The paper takes $\mathbf D^{(1)},\dots,\mathbf D^{(s)}$ to be "cut matrices as defined in Theorem 2", the output of a randomized algorithm whose error satisfies $\|\mathbf A-\mathbf D\|_C\le\epsilon\sqrt{mn}\|\mathbf A\|_F=\epsilon n\|\mathbf A\|_F\le\epsilon n^2$ (for a $0/1$ matrix $\|\mathbf A\|_F\le n$). The proof of (50) uses only this error bound, so the formal statement takes it as the hypothesis, for all pairs $S,T\subseteq V$ (the cut norm is a maximum over all pairs); the paper's proof phrases it through the symmetrised error $\bar{\mathbf W}$, which is not needed when the bound is assumed for $\mathbf A-\mathbf D$ directly. The width of the decomposition plays no role in (50) and is not constrained. The partition is Mathlib's `Finpartition.atomise` of $\{R_t\}\cup\{C_t\}$. The diagonal densities $d_{i,i}$ in $\Delta_{\mathcal P}$ are block averages, as explained in the definitions item.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 204, §5.1, claim (50); proof on p. 205

import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem claim_50 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ)
    (hD : ∀ S T : Finset V,
      |blockSum (G.adjMatrix ℝ - cutSum Rs Cs d) S T| ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    IsPseudoRegular G (atomPartition Rs Cs) (2 * ε) := by sorry

end FriezeKannan.PseudoReg
