-- Prove2me | Theorems.Thm_KMSHolder_araki_continuation_exists_unique
-- name    : KMSHolder.araki_continuation_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:50.752021+00:00
-- url     : https://prove2.me/theorems/e9d0e63b-f4d0-4b2a-b784-b4f8398ecc6b
-- title:
--   Araki's multiple-time correlation $\omega(A_n\Delta^{z_n}\cdots A_1\Delta^{z_1}A_0)$ exists and is unique on $I^{(n)}$
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with cyclic and separating unit vector $\Omega$ and modular operator $\Delta$, and let $A_0, \dots, A_n \in M$. Consider the real-time correlation
--
--   $$
--   F_A(s_1, \dots, s_n) = \langle \Omega,\ A_n\Delta^{is_n} \cdots A_1 \Delta^{is_1} A_0\, \Omega\rangle, \qquad s \in \mathbb R^n .
--   $$
--
--   Then $F_A$ has an analytic continuation to the tube $I^{(n)} = \{ z \in \mathbb C^n : \Re z_j \ge 0,\ \sum_j \Re z_j \le 1\}$: there is a function $G$, continuous on $I^{(n)}$ and holomorphic in its interior, with $G(is_1, \dots, is_n) = F_A(s)$ for all real $s$. Any two such functions agree on $I^{(n)}$.
--
--   The common value $G(z)$ is Araki's multiple-time correlation $\omega(A_n\Delta^{z_n}\cdots A_1\Delta^{z_1}A_0)$, which the paper uses in the definition (2) of $|||A|||_p$ and in the Hölder inequality (3). The statement makes the symbolic notation well defined.
--
--   Differences from the source:
--   - generalization: a $(\tau,\beta)$-KMS state $\omega_\beta$ with $e^{-\beta L}$ → any von Neumann algebra with cyclic separating unit vector, with $\Delta^z$ in place of $e^{-z\beta L}$; reason: the paper identifies $\Delta^{1/2} = e^{-\beta L/2}$ (pp.2, 4) and a KMS state's GNS data are such data, so the source case is an instance.
--   - generalization: positive $A_j$ in (2), (3) → all $A_0, \dots, A_n \in M$, every $n \ge 0$; reason: Araki's multiple-time analyticity holds for all elements of $M$, and the positive case is an instance.
--   - reading: "the analytic continuation of $t \mapsto F(t)$ to $F(i\beta)$", presupposed by the notation → existence and uniqueness on $I^{(n)}$ of a function continuous on the tube, holomorphic inside, with the real-time boundary values; reason: this is what makes the symbolic notation a well-defined value.
--   - encoding: paper indices $z_1, \dots, z_n$ → Lean `Fin n` indices with `z j` = $z_{j+1}$; $\Delta^{is}$ → `S.D.unitary s`; reason: Lean convention; same instances.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §2, eq. (2) and the sentence after it, p.3; eq. (5), p.5; from Araki–Masuda [3]

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_tube
import Definitions.Def_KMSHolder_realChain
import Definitions.Def_KMSHolder_IsArakiContinuation

open OAI.BoundedRecovery

namespace KMSHolder

/-- Jäkel–Robl, *The Hölder Inequality for KMS States*, arXiv:1103.3608v2, §2, sentence after
eq. (2), p.3 (Araki's symbolic notation, from Araki–Masuda [3]): "The subscript indicates the
analytic continuation of the map t ↦ F(t) ≐ ωβ(e^{itL/p}A ⋯ e^{itL/p}A) to F(iβ). To simplify the
notation we will denote F(iβ) by ωβ(e^{−βL/p}A ⋯ e^{−βL/p}A)."

The symbolic notation `ω(Aₙ Δ^{zₙ} ⋯ A₁ Δ^{z₁} A₀)` is well defined on the tube `I⁽ⁿ⁾`: for all
`A₀, …, Aₙ ∈ M` there is a function continuous on `I⁽ⁿ⁾`, holomorphic in its interior, with
boundary values `⟪Ω, Aₙ Δ^{isₙ} ⋯ A₁ Δ^{is₁} A₀ Ω⟫` at `z = (is₁, …, isₙ)`, and any two such
functions agree on `I⁽ⁿ⁾`.

**Formalization Note.**
* Standard modular data `S` replace the KMS state (`Δ = e^{−βL}`, p.2, p.4); `Δ^{is} =
  S.D.unitary s`.
* Stated for all `Aⱼ ∈ M`, not only positive ones (Araki's multiple-time KMS analyticity); the
  paper uses it for positive `Aⱼ` in (2), (3) and (28).
* Lean index `j` of `z` is the paper's `z_{j+1}`; `A ⟨j⟩` is `Aⱼ`. -/
theorem araki_continuation_exists_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) (n : ℕ)
    (A : Fin (n + 1) → H →L[ℂ] H) (hA : ∀ j, A j ∈ S.M) :
    (∃ G : (Fin n → ℂ) → ℂ, IsArakiContinuation S A G) ∧
      ∀ G₁ G₂ : (Fin n → ℂ) → ℂ, IsArakiContinuation S A G₁ → IsArakiContinuation S A G₂ →
        Set.EqOn G₁ G₂ (tube n 1) := by sorry

end KMSHolder
