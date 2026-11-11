-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_4
-- name    : GapAgnosticGS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:00.264538+00:00
-- url     : https://prove2.me/theorems/4d1dbea5-b204-4d75-8579-bb7fac2a80e2
-- title:
--   Lemma 3.4 — the hidden-branch Grover iterate is a rotation by $2\theta_j$ on each branch
-- statement:
--   Let $E$ be a hidden-basis environment, $Q$ the Grover iterate of Eq. (1), and $\mathcal H_j$ the branch subspace of arm $j$. Then $Q\mathcal H_j\subseteq\mathcal H_j$. Moreover, if $0<p_j<1$, put
--
--   $$|g_j\rangle=\frac{|\phi_j\rangle\Pi|\mathrm{arm}_j\rangle}{\sqrt{p_j}},\qquad |b_j\rangle=\frac{|\phi_j\rangle(I-\Pi)|\mathrm{arm}_j\rangle}{\sqrt{1-p_j}},\qquad \theta_j=\arcsin\sqrt{p_j};$$
--
--   then
--
--   $$Q|g_j\rangle=\cos(2\theta_j)|g_j\rangle-\sin(2\theta_j)|b_j\rangle,\qquad Q|b_j\rangle=\sin(2\theta_j)|g_j\rangle+\cos(2\theta_j)|b_j\rangle ,$$
--
--   i.e. $Q$ restricted to $\mathcal H_j$ is the rotation by angle $2\theta_j$ in the ordered basis $(|g_j\rangle,|b_j\rangle)$. Its eigenvectors $(|g_j\rangle\pm i|b_j\rangle)/\sqrt2$ have eigenphases $\theta_j/\pi$ and $1-\theta_j/\pi$, so phase estimation on $Q$ reads off $p_j=\sin^2\theta_j$ branch by branch without mixing the hidden branches.
--
--   Differences from the source:
--   - reading: Q|H_j is a rotation by angle 2θ_j in the ordered basis (|g_j⟩, |b_j⟩) → Q g_j = cos(2θ_j) g_j − sin(2θ_j) b_j and Q b_j = sin(2θ_j) g_j + cos(2θ_j) b_j; reason: the direction the matrices of Eq. (1) produce, with its leading minus sign; it is the one consistent with the eigenphases θ_j/π and 1 − θ_j/π printed after the lemma (p.10)
--   - encoding: H_j is invariant under Q → Q v ∈ H_j for every v ∈ H_j; reason: definition of invariance
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.4 (Hidden-branch Grover rotation) and its proof, p.10 (PDF p.11)

import Definitions.Def_GapAgnosticGS_groverQ
import Definitions.Def_GapAgnosticGS_branchSubspace
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.4 (Hidden-branch Grover rotation), p.10 (PDF p.11): "For a given HidQMAB
environment E, let H_j be the two-dimensional subspace spanned by {|ϕ_j⟩⊗Π|arm_j⟩,
|ϕ_j⟩⊗(I−Π)|arm_j⟩} or the one-dimensional span of E|ϕ_j, 0⟩ if p_j ∈ {0, 1}. Then H_j is
invariant under Q. Moreover, for 0 < p_j < 1, in the ordered basis (|g_j⟩, |b_j⟩), Q|_{H_j} is a
rotation by angle 2θ_j, where θ_j := arcsin(√p_j)." The proof (p.10) defines
`|g_j⟩ := |ϕ_j⟩Π|arm_j⟩/√p_j` and `|b_j⟩ := |ϕ_j⟩(I−Π)|arm_j⟩/√(1−p_j)`.

For every environment and arm `j`: `Q` (Eq. (1)) maps `H_j` into itself, and for `0 < p_j < 1`,
`Q g_j = cos(2θ_j) g_j − sin(2θ_j) b_j` and `Q b_j = sin(2θ_j) g_j + cos(2θ_j) b_j`.

**Formalization Note.** The rotation's direction is the one produced by Eq. (1) with its leading
minus sign (as the proof says), and it is the one consistent with the eigenphases printed after
the lemma (p.10): `(|g_j⟩ ± i|b_j⟩)/√2` with phases `θ_j/π` and `1 − θ_j/π`. -/
theorem lemma_3_4 {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A} {Prj : Matrix A A ℂ}
    (Env : HidEnv n A a₀ Prj) (j : Fin n) :
    (∀ v ∈ branchSubspace Env j, act (groverQ Env) v ∈ branchSubspace Env j) ∧
    (0 < reward Env j → reward Env j < 1 →
      let p := reward Env j
      let θ := Real.arcsin (Real.sqrt p)
      let g : EuclideanSpace ℂ (Fin n × A) :=
        ((Real.sqrt p)⁻¹ : ℂ) • tensorVec (Env.φ j) (act Prj (Env.arm j))
      let b : EuclideanSpace ℂ (Fin n × A) :=
        ((Real.sqrt (1 - p))⁻¹ : ℂ) • tensorVec (Env.φ j) (act (1 - Prj) (Env.arm j))
      act (groverQ Env) g = (Real.cos (2 * θ) : ℂ) • g - (Real.sin (2 * θ) : ℂ) • b ∧
      act (groverQ Env) b = (Real.sin (2 * θ) : ℂ) • g + (Real.cos (2 * θ) : ℂ) • b) := by sorry

end GapAgnosticGS
