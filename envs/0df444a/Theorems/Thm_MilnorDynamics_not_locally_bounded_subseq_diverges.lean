-- Prove2me | Theorems.Thm_MilnorDynamics_not_locally_bounded_subseq_diverges
-- name    : MilnorDynamics.not_locally_bounded_subseq_diverges
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T18:30:35.721769+00:00
-- url     : https://prove2.me/theorems/5d76d29e-9f6f-4e55-9814-e5b5ed06cb62
-- title:
--   Montel escape step — an unbounded holomorphic family has an escaping subsequence
-- statement:
--   **The escape step of Montel's theorem.** Let $U\subseteq\mathbb C$ be a connected open set and let $f_n:U\to\mathbb C\setminus\{0,1\}$ be holomorphic maps. Suppose the family $(f_n)$ is **not locally bounded**: there is a compact $K\subseteq U$ such that $\sup_{n}\sup_{z\in K}|f_n(z)|=\infty$. Then some subsequence $(f_{\varphi(n)})$ **diverges locally uniformly from** $\mathbb C\setminus\{0,1\}$: for every compact $K_0\subseteq U$ and every compact $K'\subseteq\mathbb C\setminus\{0,1\}$ one has $f_{\varphi(n)}(K_0)\cap K'=\emptyset$ for all sufficiently large $n$; that is, $\lvert f_{\varphi(n)}\rvert\to\infty$ locally uniformly on $U$.
--
--   **Proof.** Put $s_n=\sup_{z\in K}\lvert f_n(z)\rvert$. Each $s_n$ is finite, since $f_n$ is continuous on the compact set $K$, and $(s_n)$ is unbounded by hypothesis, so $\{n:s_n>j\}$ is infinite for every $j$; a diagonal choice gives a strictly increasing $\varphi$ with $s_{\varphi(n)}\to\infty$. As $f_n$ omits $0$, the maps $h_n=1/f_n$ are holomorphic on $U$ and bounded on each compact subset of $U$, so a further subsequence of $h_{\varphi(\cdot)}$ converges locally uniformly to some $h:\mathbb C\to\mathbb C$ (Arzel\`a\`{}-Ascoli). Since $\inf_K\lvert h_{\varphi(n)}\rvert\to0$, we have $h\equiv 0$ on $K$, hence by the identity theorem $h\equiv0$ on $U$, so $\lvert f_{\varphi(n)}\rvert\to\infty$ on every compact subset of $U$. As a compact $K'\subseteq\mathbb C\setminus\{0,1\}$ is bounded, the values eventually avoid it.
--
--   **Why a subsequence and not the whole sequence.** The conclusion is genuinely about a subsequence. Unboundedness does **not** force every term to escape: on $U=\mathbb D$ the family $f_{2m}(z)=4m/(2+z)$, $f_{2m+1}(z)=\tfrac12+\tfrac z4$ omits $\{0,1\}$ pointwise, is not locally bounded, yet every odd term has $f_{2m+1}(0)=\tfrac12$ in the compact set $\overline B(\tfrac12,\tfrac18)\subseteq\mathbb C\setminus\{0,1\}$. Only the even subsequence escapes. This is why $\varphi$ is existentially quantified here.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, pp. 32-34: the 'otherwise the family is not locally bounded, hence it diverges from every compact subset of the target' step of Montel's theorem, used in the proof of Corollary 3.3. This formulation corrects the previously published MilnorDynamics.not_locally_bounded_diverges (theorem 3c632077-6f90-4a04-80b6-89b663e0f2f9), which incorrectly demanded that the whole sequence escape with phi = id; the counterexample given above refutes that statement, while the present one is the faithful form needed by MilnorDynamics.IsNormalFamilyInto, which leaves phi existentially free

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem not_locally_bounded_subseq_diverges (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      DivergesLocallyUniformlyFrom (fun n => f (φ n)) U ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
