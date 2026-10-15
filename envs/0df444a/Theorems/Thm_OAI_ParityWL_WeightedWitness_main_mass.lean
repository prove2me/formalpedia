-- Prove2me | Theorems.Thm_OAI_ParityWL_WeightedWitness_main_mass
-- name    : OAI.ParityWL.WeightedWitness.main_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:29.435915+00:00
-- url     : https://prove2.me/theorems/7decd6df-6a4f-44be-814e-8e1f812c3751
-- title:
--   In a witness for the star parity every main template type has total mass one
-- statement:
--   Fix $t\ge1$ and let $T_t$ be the template graph: it has $t$ main vertices $m_0,\dots,m_{t-1}$, which form a clique, and one helper vertex for each pair of main indices $i<j$ together with a third index $l\notin\{i,j\}$, adjacent exactly to $m_i$, $m_j$ and $m_l$. The star parity $\beta_t:V(T_t)\to\mathbb{F}_2$ takes the value $1$ at $m_0$ and $0$ at every other vertex, where $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$.
--
--   Let $F$ be a simple graph on a finite set $W$, let $a:F\to T_t$ be a graph homomorphism, and let $(\omega,\varepsilon)$ be a weighted witness for $a$ and $\beta_t$: $\omega:W\to\mathbb{F}_2$ and $\varepsilon:W\times W\to\mathbb{F}_2$, with $\varepsilon$ symmetric and zero on non-edges of $F$, $\sum_{y\in W,\ a(y)=c}\varepsilon(x,y)=\omega(x)$ for every $x\in W$ and every neighbour $c$ of $a(x)$ in $T_t$, and $\sum_{x\in W}\omega(x)\,\beta_t(a(x))=1$. Then for every main index $i\in\{0,\dots,t-1\}$,
--   $$
--   \mu_W(m_i)=\sum_{x\in W,\ a(x)=m_i}\omega(x)=1\quad\text{in }\mathbb{F}_2 .
--   $$
--   Equivalently, for each $i$ the number of vertices $x$ of type $m_i$ with $\omega(x)=1$ is odd.
--
--   The theorem fixes the total mass of every main type in a witness for the star parity. In the parity reduction this global normalization is combined with the local conservation of mass across separators of a tree decomposition of $F$ in order to extract a successful choice from a witness.
--
--   **Formalization Note** The template is `template t` with main vertices `.inl i` for `i : Fin t`, the star parity is `starParity t`, the witness is `w : WeightedWitness (template t) F a (starParity t)`, and $\mu_W(m_i)$ is `w.mass Finset.univ (.inl i)`. The hypothesis $0<t$ guarantees that the main index $0$ exists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Masses.lean#L103-L116

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

theorem OAI.ParityWL.WeightedWitness.main_mass (w : WeightedWitness (template t) F a (starParity t))
    (ht : 0 < t) (i : Fin t) : w.mass Finset.univ (.inl i) = 1 := by sorry
