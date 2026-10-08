-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_theorem_6_hamiltonian_iff
-- name    : GilmoreGomoryTSP.Bottleneck.theorem_6_hamiltonian_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:05.749316+00:00
-- url     : https://prove2.me/theorems/f6cd7612-c359-42df-9771-35319a921466
-- title:
--   Theorem 6 (corrected) — a nested directed graph has a Hamiltonian circuit iff every φ(q) ∈ Γ_q and G′_φ is connected
-- statement:
--   Let $G$ be a directed graph on the nodes $1,\dots,N$ and let $\Gamma_i$ be the set of nodes $j$ for which $G$ has an arc from $i$ to $j$. Assume
--   $$\Gamma_1\subseteq\Gamma_2\subseteq\cdots\subseteq\Gamma_N = \{1,\dots,N\},$$
--   and let $\varphi$ be a permutation such that every $\Gamma_i$ is an initial segment $\{\varphi(1),\dots,\varphi(j)\}$ (possibly empty). Let $G'_\varphi$ be the undirected graph on the $N$ nodes with an arc $R_{q\varphi(q)}$ iff $\varphi(q)\in\Gamma_q$ and an arc $R_{q,q+1}$ iff $\varphi(q+1)\in\Gamma_q$. Then $G$ has a Hamiltonian circuit — a tour $\psi$ with $\psi(i)\in\Gamma_i$ for all $i$ — if and only if
--   $$ \varphi(q)\in\Gamma_q \ \text{for all } q \qquad\text{and}\qquad G'_\varphi \text{ is connected}.$$
--
--   This characterizes Hamiltonicity for the class of directed graphs whose out-neighbourhoods form a chain.
--
--   **Formalization Note** As printed, Theorem 6 says the circuit exists iff $G'_\varphi$ is connected. The sufficiency half of that is false: for $N=3$, $\Gamma_1=\Gamma_2=\{3\}$, $\Gamma_3=\{1,2,3\}$, $\varphi=(3,1,2)$, $G'_\varphi$ has the arcs $R_{13}$, $R_{32}$ and is connected, but nodes 1 and 2 both have the single successor 3, so no Hamiltonian circuit exists. The paper's proof needs $m(\varphi)=0$, i.e. $\varphi(q)\in\Gamma_q$ for all $q$, which it omits. The Lean adds this condition to the right-hand side; the necessity half as printed is a consequence of the corrected statement. The paper's claim that such a $\varphi$ always exists is not stated; $\varphi$ is a given permutation with the initial-segment property, where the empty segment ($j=0$) is allowed.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 671, Theorem 6 (corrected: added the condition φ(q) ∈ Γ_q)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem theorem_6_hamiltonian_iff {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1)))
    (hΓ : Monotone Γ) (hΓn : Γ (Fin.last n) = Finset.univ) (φ : Equiv.Perm (Fin (n + 1)))
    (hφ : ∀ i, ∃ j : ℕ,
      Γ i = (Finset.univ.filter (fun k : Fin (n + 1) => (k : ℕ) < j)).map φ.toEmbedding) :
    (∃ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ ∧ ∀ i, ψ i ∈ Γ i) ↔
      (∀ q, φ q ∈ Γ q) ∧ (Gprime Γ φ).Connected := by sorry

end GilmoreGomoryTSP.Bottleneck
