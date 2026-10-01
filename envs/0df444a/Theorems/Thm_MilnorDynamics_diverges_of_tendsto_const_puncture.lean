-- Prove2me | Theorems.Thm_MilnorDynamics_diverges_of_tendsto_const_puncture
-- name    : MilnorDynamics.diverges_of_tendsto_const_puncture
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:21:53.983122+00:00
-- url     : https://prove2.me/theorems/0ba1e3e1-1f78-449c-ba6a-6159e1d9e28c
-- title:
--   A family converging locally uniformly to a puncture diverges from C minus {0,1}
-- statement:
--   **A constant puncture limit forces locally uniform divergence.** Let $U\subseteq\mathbb C$ be an open set, let $f_n:\mathbb C\to\mathbb C$ be a sequence of functions and let $c\in\mathbb C$ be a point which is *not* in $\mathbb C\setminus\{0,1\}$, that is $c\in\{0,1\}$. If $f_n$ converges to the constant function $c$ locally uniformly on $U$, then $f_n$ diverges locally uniformly from $\mathbb C\setminus\{0,1\}$.
--
--   Concretely: for every compact $K\subseteq U$ and every compact $K'\subseteq\mathbb C\setminus\{0,1\}$ there is $N$ with $f_n(x)\notin K'$ for all $n\ge N$ and all $x\in K$.
--
--   The reason is a separation of scales: a compact subset of $\mathbb C\setminus\{0,1\}$ stays a positive distance away from $\{0,1\}$, because $c\notin K'$ and $K'$ is compact, hence closed. Choose $\delta$ with $\delta\le|z-c|$ for all $z\in K'$; on the compact $K$ the convergence to $c$ is uniform, so for all large $n$ the image $f_n(K)$ lies in the ball of radius $\delta$ about $c$, which is disjoint from $K'$.
--
--   This is the branch of the Hurwitz dichotomy that involves no holomorphy: it is the elementary half of the statement that a planar limit of a holomorphic family either avoids $\{0,1\}$ or forces local uniform divergence from $\mathbb C\setminus\{0,1\}$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Lemma 3.1(a) and the definition of locally uniform divergence on p. 33: on a compact set the spherical and Euclidean metrics are uniformly equivalent, and a compact subset of $\mathbb C\setminus\{0,1\}$ keeps a positive Euclidean distance from $\{0,1\}$, so uniform convergence to a puncture forces escape from every compact subset of the complement.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem diverges_of_tendsto_const_puncture (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ) (c : ℂ)
    (hcov : TendstoLocallyUniformlyOn f (fun _ => c) atTop U)
    (hc : c ∉ ({0, 1}ᶜ : Set ℂ)) :
    DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
