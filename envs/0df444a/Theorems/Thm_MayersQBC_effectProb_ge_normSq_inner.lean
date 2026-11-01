-- Prove2me | Theorems.Thm_MayersQBC_effectProb_ge_normSq_inner
-- name    : MayersQBC.effectProb_ge_normSq_inner
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:12.211643+00:00
-- url     : https://prove2.me/theorems/c8fd7646-9294-4538-8620-ed8144aa87f7
-- title:
--   Section e, p.4 — an effect accepting $\psi$ with certainty accepts $\varphi$ with probability $\ge |\langle\varphi|\psi\rangle|^2$
-- statement:
--   Let $E$ be an effect on a finite-dimensional system, $0 \preceq E \preceq I$, and let $\psi$ be a unit vector that $E$ accepts with certainty, $\langle\psi|E|\psi\rangle = 1$. Then for every vector $\varphi$,
--
--   $$
--   |\langle\varphi|\psi\rangle|^2 \le \langle\varphi|E|\varphi\rangle .
--   $$
--
--   This is the operator fact behind the paper's step "Inequality 4 implies that the probability $p_\gamma$ that unveil′ returns 1 on $|\psi'_{0,\gamma}\rangle$ is greater than $f(F'(\gamma))$", whose details the paper defers to its reference [12]: with $E$ the honest unveil of $1$, which accepts $\psi'_{1,\gamma}$ with certainty by correctness, and $\varphi = \psi_{01}$, it bounds Alice's success probability by the squared overlap from (4).
--
--   **Formalization Note** $\langle\varphi|E|\varphi\rangle$ is `effectProb E (pureDensity φ)` $= \operatorname{Re}\operatorname{Tr}(E|\varphi\rangle\langle\varphi|)$; `IsEffect E` is $0 \preceq E \preceq I$. $\varphi$ need not be a unit vector.
--
--   Differences from the source:
--   - generalization: the implication from (4) to the bound on p_γ, for the honest unveil of 1, ψ′1,γ and ψ01 (details in [12]) → |⟨φ|ψ⟩|² ≤ ⟨φ|E|φ⟩ for every effect E, every unit ψ with ⟨ψ|E|ψ⟩ = 1 and every vector φ; reason: the page's use is the special case E = honest unveil of 1, ψ = ψ′1,γ, φ = ψ01
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, third step, p.4 ("Alice in unveil′ can transform |ψ′0,γ⟩ into |ψ01⟩ … and then continue with the honest unveil. Inequality 4 implies …", details in [12])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section e, third step, p.4: the operator fact behind
"The fact that |ψ01⟩ is a purification of ρB(|ψ′0,γ⟩) implies that Alice in unveil′ can transform
|ψ′0,γ⟩ into |ψ01⟩, as in the case where the density matrices are identical, and then continue
with the honest unveil. Inequality 4 implies that the probability pγ that unveil′ returns 1 …"
(the details are deferred by the paper to [12]). Let `E` be an effect (`0 ⪯ E ⪯ I`) and `ψ` a
unit vector that `E` accepts with certainty, `⟨ψ|E|ψ⟩ = 1`. Then every vector `φ` is accepted
with probability at least its squared overlap with `ψ`: `|⟨φ|ψ⟩|² ≤ ⟨φ|E|φ⟩`.

**Formalization Note.** `effectProb E (pureDensity φ) = Re Tr(E |φ⟩⟨φ|) = ⟨φ|E|φ⟩`. `φ` is any
vector, not necessarily of norm one. -/
theorem effectProb_ge_normSq_inner {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : IsEffect E) (ψ φ : EuclideanSpace ℂ ι) (hψ : IsState ψ)
    (hacc : effectProb E (pureDensity ψ) = 1) :
    ‖inner ℂ φ ψ‖ ^ 2 ≤ effectProb E (pureDensity φ) := by sorry

end MayersQBC
