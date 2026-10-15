-- Prove2me | Theorems.Thm_OAI_QAC_toffoli_reflection
-- name    : OAI.QAC.toffoli_reflection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:49:46.244001+00:00
-- url     : https://prove2.me/theorems/fb6b8584-8bb8-4b01-972f-3c7171523496
-- title:
--   Every Toffoli gate is a reflection $I-2P$ about a product projection
-- statement:
--   Consider $N$ qubits indexed by $\{0,\dots,N-1\}$, with computational basis $\{|x\rangle : x\in\{0,1\}^N\}$. Let $c\subseteq\{0,\dots,N-1\}$ be a set of control qubits and let $t$ be a target qubit with $t\notin c$. For $y\in\{0,1\}^N$ let $\tau(y)$ be the word obtained from $y$ by flipping bit $t$ if $y_i=1$ for every $i\in c$, and $\tau(y)=y$ otherwise. The Toffoli gate $\mathrm{TOF}_{c,t}$ is the permutation matrix sending $|y\rangle$ to $|\tau(y)\rangle$, i.e. $(\mathrm{TOF}_{c,t})_{x,y}=1$ if $x=\tau(y)$ and $0$ otherwise. Let $|-\rangle=\tfrac{1}{\sqrt2}\bigl(|0\rangle-|1\rangle\bigr)$. Then
--
--   $$
--   \mathrm{TOF}_{c,t}=I-2\,P_{c,t},\qquad P_{c,t}=|-\rangle\langle-|_{t}\ \otimes\ \bigotimes_{i\in c}|1\rangle\langle1|_{i}\ \otimes\ I_{\mathrm{rest}},
--   $$
--
--   where $I_{\mathrm{rest}}$ is the identity on the qubits outside $c\cup\{t\}$. In the language of counts, $P_{c,t}=P^0_{T_{c,t}}$ is the zero-mismatch projection of the count $T_{c,t}$ with support $c\cup\{t\}$, axis $|-\rangle$ on the target and axis $|1\rangle$ on every control.
--
--   Since $P_{c,t}$ is an orthogonal projection, the identity exhibits every Toffoli gate, with an arbitrary number of controls, as a reflection about a product projection whose support is exactly the support of the gate (for $c=\emptyset$ it reduces to $X=I-2|-\rangle\langle-|$ on qubit $t$). This is what allows a physical layer of one-qubit gates and unbounded-arity Toffoli gates to be rewritten as a layer of disjoint reflections, the normal form on which the localization theorem for constant-depth circuits operates.
--
--   **Formalization Note** The left side is `Gate.matrix (.toffoli c t ht)`, whose entries do not depend on the proof `ht` of $t\notin c$; the right side is `reflect (toffoliCount c t)`, defined as `1 - (2:ℝ) • (toffoliCount c t).zero`. The count `toffoliCount c t` also assigns the axis $|1\rangle$ to qubits outside its support, where it plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean#L88-L124

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem OAI.QAC.toffoli_reflection {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c) :
    Gate.matrix (.toffoli c t ht) = reflect (toffoliCount c t) := by sorry
